/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    kconfirm_solver.cpp

Abstract:

    Compile a Boolean formula with difference bounds and string equality
    onto sat::solver. Definitions of the form (= x F) reuse F's literal.
    Integer and string atoms are checked only after a complete SAT candidate.
    Anything outside that fragment is handed to the ordinary SMT solver.

--*/
#include "tactic/kconfirm/kconfirm_solver.h"
#include "solver/solver_na2as.h"
#include "solver/solver2tactic.h"
#include "smt/smt_solver.h"
#include "smt/diff_logic.h"
#include "sat/sat_solver.h"
#include "sat/sat_extension.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_translation.h"
#include "model/model.h"
#include "util/uint_set.h"
#include <algorithm>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

namespace {

class kconfirm_solver;

struct kc_ext {
    typedef rational numeral;
    typedef sat::literal explanation;
};

struct lin {
    expr*    v[2] = { nullptr, nullptr };
    int      coeff[2] = { 0, 0 };
    unsigned n = 0;
    rational c;
    bool     ok = true;

    bool add_var(expr* var, int k) {
        if (!ok)
            return false;
        for (unsigned i = 0; i < n; ++i) {
            if (v[i] != var)
                continue;
            coeff[i] += k;
            if (coeff[i] == 0) {
                v[i] = v[n - 1];
                coeff[i] = coeff[n - 1];
                --n;
            }
            else if (coeff[i] != 1 && coeff[i] != -1) {
                ok = false;
                return false;
            }
            return true;
        }
        if (k == 0)
            return true;
        if (n >= 2 || (k != 1 && k != -1)) {
            ok = false;
            return false;
        }
        v[n] = var;
        coeff[n] = k;
        ++n;
        return true;
    }

    void add_const(rational const& k) { c += k; }

    void negate() {
        c.neg();
        for (unsigned i = 0; i < n; ++i)
            coeff[i] = -coeff[i];
    }

    bool add_lin(lin const& o) {
        if (!ok || !o.ok) {
            ok = false;
            return false;
        }
        c += o.c;
        for (unsigned i = 0; i < o.n; ++i)
            if (!add_var(o.v[i], o.coeff[i]))
                return false;
        return ok;
    }
};

class kc_theory : public sat::extension {
    kconfirm_solver& m_owner;
public:
    kc_theory(kconfirm_solver& owner): sat::extension(symbol("kconfirm"), 0), m_owner(owner) {}
    bool unit_propagate() override { return false; }
    void get_antecedents(sat::literal, sat::ext_justification_idx, sat::literal_vector&, bool) override {}
    sat::check_result check() override;
    void asserted(sat::literal l) override;
    void push() override;
    void pop(unsigned n) override;
    std::ostream& display(std::ostream& out) const override { return out; }
    std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx) const override { return out; }
    std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx) const override { return out; }
};

class kconfirm_solver : public solver_na2as {
    friend class kc_theory;
    struct iatom {
        sat::literal lit;
        dl_var       src;
        dl_var       dst;
        rational     w;
    };
    struct satom {
        sat::literal lit;
        unsigned     a;
        unsigned     b;
    };
    struct snode {
        unsigned parent = 0;
        bool     is_cst = false;
        bool     class_has = false;
        unsigned cst_node = UINT_MAX;
        zstring  cst;
    };
    struct sedge {
        unsigned     n;
        sat::literal lit;
    };

    params_ref             m_params;
    expr_ref_vector        m_assertions;
    expr_ref_vector        m_pinned;
    unsigned_vector        m_limits;
    arith_util             m_arith;
    seq_util               m_seq;
    sat::solver*           m_sat = nullptr;
    sat::literal           m_true;
    bool                   m_dirty = true;
    bool                   m_failed = false;
    expr*                  m_fail = nullptr;
    obj_map<expr, expr*>   m_def;
    obj_map<expr, sat::literal> m_cache;
    obj_hashtable<expr>    m_on_stack;
    ptr_vector<expr>       m_bools;
    sat::literal_vector    m_bool_lits;
    vector<iatom>          m_iatoms;
    vector<satom>          m_satoms;
    obj_map<expr, dl_var>  m_int_var;
    ptr_vector<expr>       m_int_exprs;
    obj_map<expr, unsigned> m_str_var;
    vector<snode>          m_nodes;
    vector<svector<sedge>> m_adj;
    ptr_vector<expr>       m_str_exprs;
    unsigned_vector        m_str_ids;
    vector<rational>       m_model_int;
    vector<zstring>        m_model_str;
    vector<zstring>        m_str_consts;
    sat::literal_vector    m_core_lits;
    ptr_vector<expr>       m_core_exprs;
    unsigned               m_aliases = 0;
    unsigned               m_ladders = 0;
    // One-step consequences of tristate ladders: y => m and not m => not y.
    std::unordered_map<unsigned, sat::literal> m_implies;
    std::map<std::vector<unsigned>, sat::literal> m_and_gate;
    unsigned               m_th_conflicts = 0;
    unsigned               m_fallback_n = 0;
    unsigned               m_int_undef = 0;
    unsigned               m_str_undef = 0;
    unsigned               m_local_clauses = 0;
    dl_graph<kc_ext>*      m_dl = nullptr;
    svector<int>           m_int_of_var;
    svector<char>          m_int_on;
    unsigned_vector        m_int_trail;
    unsigned_vector        m_int_lim;
    bool                   m_model_ready = false;
    ref<solver>            m_fb;
    std::string            m_unknown = "unknown";

    expr* assertion_at(unsigned i) const {
        return static_cast<expr_ref_vector const&>(m_assertions)[i];
    }

    expr* pin(expr* e) {
        m_pinned.push_back(e);
        return e;
    }

    void fail(expr* e) {
        if (m_failed)
            return;
        m_failed = true;
        m_fail = e;
    }

    void reset_encoding() {
        if (m_dl) {
            dealloc(m_dl);
            m_dl = nullptr;
        }
        m_int_of_var.reset();
        m_int_on.reset();
        m_int_trail.reset();
        m_int_lim.reset();
        if (m_sat) {
            dealloc(m_sat);
            m_sat = nullptr;
        }
        m_cache.reset();
        m_def.reset();
        m_on_stack.reset();
        m_bools.reset();
        m_bool_lits.reset();
        m_iatoms.reset();
        m_satoms.reset();
        m_int_var.reset();
        m_int_exprs.reset();
        m_str_var.reset();
        m_nodes.reset();
        m_adj.reset();
        m_str_exprs.reset();
        m_str_ids.reset();
        m_model_int.reset();
        m_model_str.reset();
        m_str_consts.reset();
        m_pinned.reset();
        m_failed = false;
        m_fail = nullptr;
        m_local_clauses = 0;
        m_model_ready = false;
        m_aliases = 0;
        m_ladders = 0;
        m_implies.clear();
        m_and_gate.clear();
    }

    bool occurs(expr* e, expr* x) {
        ast_mark seen;
        ptr_vector<expr> todo;
        todo.push_back(e);
        while (!todo.empty()) {
            expr* n = todo.back();
            todo.pop_back();
            if (n == x)
                return true;
            if (seen.is_marked(n))
                continue;
            seen.mark(n, true);
            if (is_app(n))
                for (expr* a : *to_app(n))
                    todo.push_back(a);
        }
        return false;
    }

    bool is_def(expr* e, expr*& var, expr*& body) {
        expr* a = nullptr;
        expr* b = nullptr;
        if (!m.is_iff(e, a, b))
            return false;
        if (is_uninterp_const(a) && a != b && !occurs(b, a)) {
            var = a;
            body = b;
            return true;
        }
        if (is_uninterp_const(b) && a != b && !occurs(a, b)) {
            var = b;
            body = a;
            return true;
        }
        return false;
    }

    void flatten(expr* e, ptr_vector<expr>& out) {
        if (m.is_and(e)) {
            for (expr* a : *to_app(e))
                flatten(a, out);
        }
        else {
            out.push_back(e);
        }
    }

    void remember(expr* e, sat::literal l) {
        if (is_uninterp_const(e) && m.is_bool(e)) {
            m_bools.push_back(e);
            m_bool_lits.push_back(l);
        }
    }

    // Boolean constants and theory atoms stay external so elimination and
    // assumption tracking leave them in the model. Gate variables do not.
    sat::literal fresh() {
        return sat::literal(m_sat->mk_var(true, true), false);
    }

    sat::literal fresh_gate() {
        return sat::literal(m_sat->mk_var(false, true), false);
    }

    void add_clause(unsigned n, sat::literal* ls) {
        if (m_failed)
            return;
        for (unsigned i = 0; i < n; ++i)
            if (ls[i] == m_true)
                return;
        m_sat->mk_clause(n, ls, sat::status::asserted());
    }

    void add_iff(sat::literal a, sat::literal b) {
        if (a == b)
            return;
        sat::literal c1[2] = { ~a, b };
        sat::literal c2[2] = { a, ~b };
        add_clause(2, c1);
        add_clause(2, c2);
    }

    bool level_symbol(expr* e, std::string& prefix, char& level) const {
        if (!is_uninterp_const(e) || !m.is_bool(e))
            return false;
        char const* n = to_app(e)->get_decl()->get_name().bare_str();
        unsigned len = static_cast<unsigned>(strlen(n));
        if (len < 3 || n[len - 3] != '>' || n[len - 2] != '=')
            return false;
        char lv = n[len - 1];
        if (lv != 'y' && lv != 'm')
            return false;
        prefix.assign(n, n + (len - 3));
        level = lv;
        return true;
    }

    // An unguarded (=> P>=y P>=m). Guarded copies stay ordinary clauses.
    bool ladder_ends(expr* e, expr*& hi, expr*& lo) const {
        expr* a = nullptr;
        expr* b = nullptr;
        if (m.is_implies(e) && to_app(e)->get_num_args() == 2) {
            a = to_app(e)->get_arg(0);
            b = to_app(e)->get_arg(1);
        }
        else if (m.is_or(e) && to_app(e)->get_num_args() == 2) {
            expr* x = to_app(e)->get_arg(0);
            expr* y = to_app(e)->get_arg(1);
            if (m.is_not(x)) {
                a = to_app(x)->get_arg(0);
                b = y;
            }
            else if (m.is_not(y)) {
                a = to_app(y)->get_arg(0);
                b = x;
            }
            else {
                return false;
            }
        }
        else {
            return false;
        }
        std::string pa, pb;
        char la = 0, lb = 0;
        if (!level_symbol(a, pa, la) || !level_symbol(b, pb, lb))
            return false;
        if (pa != pb || la != 'y' || lb != 'm')
            return false;
        hi = a;
        lo = b;
        return true;
    }

    void record_ladder(sat::literal hi, sat::literal lo) {
        if (hi == lo || hi == ~lo)
            return;
        if (hi == m_true || hi == ~m_true || lo == m_true || lo == ~m_true)
            return;
        if (m_implies.find(hi.index()) == m_implies.end()) {
            m_implies.emplace(hi.index(), lo);
            ++m_ladders;
        }
        if (m_implies.find((~lo).index()) == m_implies.end())
            m_implies.emplace((~lo).index(), ~hi);
    }

    sat::literal implied_by(sat::literal a) const {
        auto it = m_implies.find(a.index());
        if (it == m_implies.end())
            return sat::null_literal;
        return it->second;
    }

    void install_ladders(ptr_vector<expr> const& rest) {
        struct ends { expr* hi; expr* lo; };
        vector<ends> ls;
        for (expr* e : rest) {
            expr* hi = nullptr;
            expr* lo = nullptr;
            if (ladder_ends(e, hi, lo))
                ls.push_back(ends{hi, lo});
        }
        auto record = [&](ends const& L) {
            record_ladder(lit(L.hi), lit(L.lo));
        };
        for (ends const& L : ls)
            if (!m_def.contains(L.hi) && !m_def.contains(L.lo))
                record(L);
        for (ends const& L : ls)
            if (m_def.contains(L.hi) || m_def.contains(L.lo))
                record(L);
    }

    sat::literal lit_bool_const(expr* e) {
        expr* body = nullptr;
        if (!m_def.find(e, body)) {
            sat::literal l = fresh();
            remember(e, l);
            return l;
        }
        sat::literal cached;
        if (m_cache.find(e, cached))
            return cached;
        if (m_on_stack.contains(e)) {
            sat::literal l = fresh();
            remember(e, l);
            m_cache.insert(e, l);
            return l;
        }
        m_on_stack.insert(e);
        sat::literal b = lit(body);
        m_on_stack.erase(e);
        if (m_cache.find(e, cached)) {
            if (cached != b)
                add_iff(cached, b);
            return cached;
        }
        // The name is the body literal. Keep that variable: a later
        // check-sat-assuming names it, and elimination must not delete it.
        m_sat->set_external(b.var());
        remember(e, b);
        m_cache.insert(e, b);
        return b;
    }

    // Conjunction up to ladder consequences. hi => lo makes lo redundant
    // beside hi, and hi together with not lo is false.
    sat::literal lit_and_lits(std::vector<sat::literal> args) {
        std::vector<sat::literal> kept;
        kept.reserve(args.size());
        for (sat::literal la : args) {
            if (la == ~m_true)
                return ~m_true;
            if (la != m_true)
                kept.push_back(la);
        }
        std::sort(kept.begin(), kept.end(), [](sat::literal a, sat::literal b) {
            return a.index() < b.index();
        });
        unsigned w = 0;
        for (unsigned i = 0; i < kept.size(); ++i) {
            if (w > 0 && kept[w - 1] == kept[i])
                continue;
            if (w > 0 && kept[w - 1] == ~kept[i])
                return ~m_true;
            kept[w++] = kept[i];
        }
        kept.resize(w);
        uint_set present;
        for (sat::literal la : kept)
            present.insert(la.index());
        for (sat::literal la : kept) {
            sat::literal b = implied_by(la);
            if (b != sat::null_literal && present.contains((~b).index()))
                return ~m_true;
        }
        uint_set dropped;
        for (sat::literal la : kept) {
            if (dropped.contains(la.index()))
                continue;
            sat::literal b = implied_by(la);
            if (b == sat::null_literal || !present.contains(b.index()))
                continue;
            dropped.insert(b.index());
        }
        w = 0;
        for (sat::literal la : kept) {
            if (dropped.contains(la.index()))
                continue;
            kept[w++] = la;
        }
        kept.resize(w);
        if (kept.empty())
            return m_true;
        if (kept.size() == 1)
            return kept[0];
        std::vector<unsigned> key;
        key.reserve(kept.size());
        for (sat::literal la : kept)
            key.push_back(la.index());
        auto found = m_and_gate.find(key);
        if (found != m_and_gate.end())
            return found->second;
        sat::literal l = fresh_gate();
        for (sat::literal la : kept) {
            sat::literal cls[2] = { ~l, la };
            add_clause(2, cls);
        }
        sat::literal_vector back;
        back.push_back(l);
        for (sat::literal la : kept)
            back.push_back(~la);
        add_clause(back.size(), back.data());
        m_and_gate.emplace(std::move(key), l);
        return l;
    }

    sat::literal lit_and(expr* e) {
        std::vector<sat::literal> args;
        args.reserve(to_app(e)->get_num_args());
        for (expr* arg : *to_app(e))
            args.push_back(lit(arg));
        return lit_and_lits(std::move(args));
    }

    sat::literal lit_or(expr* e) {
        std::vector<sat::literal> args;
        args.reserve(to_app(e)->get_num_args());
        for (expr* arg : *to_app(e))
            args.push_back(~lit(arg));
        return ~lit_and_lits(std::move(args));
    }

    sat::literal lit_implies(expr* e) {
        sat::literal a = lit(to_app(e)->get_arg(0));
        sat::literal b = lit(to_app(e)->get_arg(1));
        if (a == ~m_true || b == m_true)
            return m_true;
        if (a == m_true)
            return b;
        if (b == ~m_true)
            return ~a;
        sat::literal l = fresh_gate();
        sat::literal c1[3] = { ~l, ~a, b };
        sat::literal c2[2] = { l, a };
        sat::literal c3[2] = { l, ~b };
        add_clause(3, c1);
        add_clause(2, c2);
        add_clause(2, c3);
        return l;
    }

    sat::literal lit_ite(expr* e) {
        expr* c = to_app(e)->get_arg(0);
        expr* t = to_app(e)->get_arg(1);
        expr* f = to_app(e)->get_arg(2);
        sat::literal lc = lit(c);
        sat::literal lt = lit(t);
        sat::literal lf = lit(f);
        if (lc == m_true)
            return lt;
        if (lc == ~m_true)
            return lf;
        sat::literal l = fresh_gate();
        sat::literal c1[3] = { ~lc, ~l, lt };
        sat::literal c2[3] = { ~lc, l, ~lt };
        sat::literal c3[3] = { lc, ~l, lf };
        sat::literal c4[3] = { lc, l, ~lf };
        add_clause(3, c1);
        add_clause(3, c2);
        add_clause(3, c3);
        add_clause(3, c4);
        return l;
    }

    sat::literal lit_iff_lits(sat::literal a, sat::literal b) {
        if (a == b)
            return m_true;
        if (a == ~b)
            return ~m_true;
        sat::literal l = fresh_gate();
        sat::literal c1[3] = { ~l, ~a, b };
        sat::literal c2[3] = { ~l, ~b, a };
        sat::literal c3[3] = { l, ~a, ~b };
        sat::literal c4[3] = { l, a, b };
        add_clause(3, c1);
        add_clause(3, c2);
        add_clause(3, c3);
        add_clause(3, c4);
        return l;
    }

    bool parse_lin(expr* e, lin& out) {
        rational r;
        if (m_arith.is_numeral(e, r)) {
            if (!m_arith.is_int(e) || !r.is_int())
                return false;
            out.add_const(r);
            return true;
        }
        if (is_uninterp_const(e)) {
            if (!m_arith.is_int(e))
                return false;
            return out.add_var(e, 1);
        }
        if (!is_app(e))
            return false;
        if (m_arith.is_uminus(e)) {
            lin inner;
            if (!parse_lin(to_app(e)->get_arg(0), inner))
                return false;
            inner.negate();
            return out.add_lin(inner);
        }
        if (m_arith.is_add(e)) {
            for (expr* a : *to_app(e)) {
                lin inner;
                if (!parse_lin(a, inner) || !out.add_lin(inner))
                    return false;
            }
            return true;
        }
        if (m_arith.is_sub(e)) {
            app* a = to_app(e);
            if (a->get_num_args() != 2)
                return false;
            lin lhs, rhs;
            if (!parse_lin(a->get_arg(0), lhs) || !parse_lin(a->get_arg(1), rhs))
                return false;
            rhs.negate();
            return out.add_lin(lhs) && out.add_lin(rhs);
        }
        return false;
    }

    dl_var var_of(expr* e) {
        dl_var v = 0;
        if (m_int_var.find(e, v))
            return v;
        v = static_cast<dl_var>(m_int_exprs.size() + 1);
        m_int_exprs.push_back(e);
        m_int_var.insert(e, v);
        return v;
    }

    bool edge_of(lin const& d, dl_var& src, dl_var& dst, rational& w) {
        if (!d.ok)
            return false;
        if (d.n == 1 && d.coeff[0] == 1) {
            src = 0;
            dst = var_of(d.v[0]);
            w = -d.c;
            return true;
        }
        if (d.n == 1 && d.coeff[0] == -1) {
            src = var_of(d.v[0]);
            dst = 0;
            w = -d.c;
            return true;
        }
        if (d.n == 2) {
            expr* pos = nullptr;
            expr* neg = nullptr;
            if (d.coeff[0] == 1 && d.coeff[1] == -1) {
                pos = d.v[0];
                neg = d.v[1];
            }
            else if (d.coeff[0] == -1 && d.coeff[1] == 1) {
                pos = d.v[1];
                neg = d.v[0];
            }
            else {
                return false;
            }
            src = var_of(neg);
            dst = var_of(pos);
            w = -d.c;
            return true;
        }
        return false;
    }

    app* mk_cmp(expr* sample, expr* a, expr* b) {
        if (m_arith.is_le(sample))
            return m_arith.mk_le(a, b);
        if (m_arith.is_lt(sample))
            return m_arith.mk_lt(a, b);
        if (m_arith.is_ge(sample))
            return m_arith.mk_ge(a, b);
        return m_arith.mk_gt(a, b);
    }

    sat::literal lit_cmp(expr* e) {
        expr* a = to_app(e)->get_arg(0);
        expr* b = to_app(e)->get_arg(1);
        expr* c = nullptr;
        expr* t = nullptr;
        expr* f = nullptr;
        if (m.is_ite(a, c, t, f)) {
            expr_ref e1(mk_cmp(e, t, b), m);
            expr_ref e2(mk_cmp(e, f, b), m);
            expr_ref g(m.mk_ite(c, e1, e2), m);
            return lit(pin(g));
        }
        if (m.is_ite(b, c, t, f)) {
            expr_ref e1(mk_cmp(e, a, t), m);
            expr_ref e2(mk_cmp(e, a, f), m);
            expr_ref g(m.mk_ite(c, e1, e2), m);
            return lit(pin(g));
        }
        bool swapped = false;
        bool strict = false;
        if (m_arith.is_ge(e))
            swapped = true;
        else if (m_arith.is_gt(e)) {
            swapped = true;
            strict = true;
        }
        else if (m_arith.is_lt(e))
            strict = true;
        else if (!m_arith.is_le(e)) {
            fail(e);
            return m_true;
        }
        lin left, right;
        expr* lhs = swapped ? b : a;
        expr* rhs = swapped ? a : b;
        if (!parse_lin(lhs, left) || !parse_lin(rhs, right)) {
            fail(e);
            return m_true;
        }
        right.negate();
        if (!left.add_lin(right)) {
            fail(e);
            return m_true;
        }
        if (strict)
            left.c += rational(1);
        if (left.n == 0)
            return left.c.is_pos() ? ~m_true : m_true;
        dl_var src = 0, dst = 0;
        rational w;
        if (!edge_of(left, src, dst, w)) {
            fail(e);
            return m_true;
        }
        sat::literal l = fresh();
        m_iatoms.push_back(iatom{ l, src, dst, w });
        return l;
    }

    bool str_leaf(expr* e) {
        zstring s;
        if (m_seq.str.is_string(e, s))
            return true;
        return is_uninterp_const(e) && m_seq.str.is_string_term(e);
    }

    unsigned str_node(expr* e) {
        unsigned id = 0;
        if (m_str_var.find(e, id))
            return id;
        id = m_nodes.size();
        snode nd;
        nd.parent = id;
        zstring s;
        if (m_seq.str.is_string(e, s)) {
            nd.is_cst = true;
            nd.class_has = true;
            nd.cst = s;
            nd.cst_node = id;
            m_str_consts.push_back(s);
        }
        else {
            m_str_exprs.push_back(e);
            m_str_ids.push_back(id);
        }
        m_nodes.push_back(nd);
        m_str_var.insert(e, id);
        return id;
    }

    sat::literal lit_str_eq(expr* e, expr* a, expr* b) {
        expr* c = nullptr;
        expr* t = nullptr;
        expr* f = nullptr;
        if (m.is_ite(b, c, t, f)) {
            expr_ref e1(m.mk_eq(a, t), m);
            expr_ref e2(m.mk_eq(a, f), m);
            expr_ref g(m.mk_ite(c, e1, e2), m);
            return lit(pin(g));
        }
        if (m.is_ite(a, c, t, f)) {
            expr_ref e1(m.mk_eq(t, b), m);
            expr_ref e2(m.mk_eq(f, b), m);
            expr_ref g(m.mk_ite(c, e1, e2), m);
            return lit(pin(g));
        }
        if (!str_leaf(a) || !str_leaf(b)) {
            fail(e);
            return m_true;
        }
        zstring sa, sb;
        if (m_seq.str.is_string(a, sa) && m_seq.str.is_string(b, sb))
            return sa == sb ? m_true : ~m_true;
        sat::literal l = fresh();
        m_satoms.push_back(satom{ l, str_node(a), str_node(b) });
        return l;
    }

    sat::literal lit_eq(expr* e) {
        expr* a = to_app(e)->get_arg(0);
        expr* b = to_app(e)->get_arg(1);
        if (m.is_bool(a) || m.is_bool(b)) {
            if (!(m.is_bool(a) && m.is_bool(b))) {
                fail(e);
                return m_true;
            }
            return lit_iff_lits(lit(a), lit(b));
        }
        if (m_arith.is_int(a) || m_arith.is_int(b)) {
            if (!(m_arith.is_int(a) && m_arith.is_int(b))) {
                fail(e);
                return m_true;
            }
            expr_ref le1(m_arith.mk_le(a, b), m);
            expr_ref le2(m_arith.mk_le(b, a), m);
            expr_ref both(m.mk_and(le1, le2), m);
            return lit(pin(both));
        }
        if (m_seq.str.is_string_term(a) || m_seq.str.is_string_term(b))
            return lit_str_eq(e, a, b);
        fail(e);
        return m_true;
    }

    sat::literal lit_uncached(expr* e) {
        if (m_failed)
            return m_true;
        if (is_quantifier(e) || is_var(e) || !is_app(e)) {
            fail(e);
            return m_true;
        }
        if (is_uninterp_const(e)) {
            if (m.is_bool(e))
                return lit_bool_const(e);
            fail(e);
            return m_true;
        }
        if (m.is_and(e))
            return lit_and(e);
        if (m.is_or(e))
            return lit_or(e);
        if (m.is_implies(e))
            return lit_implies(e);
        if (m.is_ite(e)) {
            if (m.is_bool(e))
                return lit_ite(e);
            fail(e);
            return m_true;
        }
        if (m.is_eq(e))
            return lit_eq(e);
        if (m_arith.is_le(e) || m_arith.is_lt(e) || m_arith.is_ge(e) || m_arith.is_gt(e))
            return lit_cmp(e);
        fail(e);
        return m_true;
    }

    sat::literal lit(expr* e) {
        if (m_failed)
            return m_true;
        if (m.is_true(e))
            return m_true;
        if (m.is_false(e))
            return ~m_true;
        if (m.is_not(e))
            return ~lit(to_app(e)->get_arg(0));
        sat::literal cached;
        if (m_cache.find(e, cached))
            return cached;
        sat::literal l = lit_uncached(e);
        if (m_cache.find(e, cached))
            return cached;
        if (!m_failed)
            m_cache.insert(e, l);
        return l;
    }

    void flatten_or(expr* e, sat::literal_vector& ls, bool& taut) {
        if (taut || m_failed)
            return;
        if (m.is_or(e)) {
            for (expr* a : *to_app(e))
                flatten_or(a, ls, taut);
            return;
        }
        sat::literal l = lit(e);
        if (l == m_true)
            taut = true;
        else if (l != ~m_true)
            ls.push_back(l);
    }

    void assert_formula(expr* e) {
        if (m_failed)
            return;
        if (m.is_or(e)) {
            sat::literal_vector ls;
            bool taut = false;
            flatten_or(e, ls, taut);
            if (!taut)
                add_clause(ls.size(), ls.data());
            return;
        }
        if (m.is_implies(e)) {
            sat::literal a = lit(to_app(e)->get_arg(0));
            sat::literal b = lit(to_app(e)->get_arg(1));
            sat::literal ls[2] = { ~a, b };
            add_clause(2, ls);
            return;
        }
        sat::literal l = lit(e);
        m_sat->add_clause(l, sat::status::asserted());
    }

    bool compile() {
        if (m_fb)
            return false;
        if (!m_dirty && m_sat)
            return true;
        reset_encoding();
        params_ref sp;
        // Resolve away gate variables. Boolean constants and theory atoms are
        // external, and the solver stays incremental, so those survive.
        // Blocked-clause passes are off: a clause that is blocked today can
        // matter once check-sat-assuming adds a unit.
        sp.set_bool("elim_vars", true);
        sp.set_bool("override_incremental", true);
        sp.set_bool("ate", false);
        sp.set_uint("bce_at", UINT_MAX);
        m_sat = alloc(sat::solver, sp, m.limit());
        m_sat->set_incremental(true);
        m_sat->updt_params(sp);
        // A conflict found after a complete assignment has to be learned
        // inside this search. Returning and calling check() again pops the
        // trail and decides the same variables over.
        m_sat->set_extension(alloc(kc_theory, *this));
        m_true = sat::literal(m_sat->mk_var(true, false), false);
        m_sat->add_clause(m_true, sat::status::asserted());
        ptr_vector<expr> flat;
        for (unsigned i = 0; i < m_assertions.size(); ++i)
            flatten(assertion_at(i), flat);
        ptr_vector<expr> rest;
        for (expr* e : flat) {
            expr* var = nullptr;
            expr* body = nullptr;
            if (is_def(e, var, body) && !m_def.contains(var)) {
                m_def.insert(var, body);
                ++m_aliases;
            }
            else {
                rest.push_back(e);
            }
        }
        // Record y => m before definitions are compiled, so conjunctions
        // can drop the redundant lower threshold.
        install_ladders(rest);
        if (m_failed)
            return false;
        for (expr* e : rest) {
            assert_formula(e);
            if (m_failed)
                return false;
        }
        // Pairs of bounds that cannot hold together become clauses here, so
        // the SAT solver rejects them by unit propagation instead of finding
        // a complete assignment and only then asking the difference graph.
        compile_local_conflicts();
        // Difference bounds are enabled as their literals are assigned.
        // Level-0 units are already on the trail, so replay them first.
        init_dl();
        // Eliminate gate variables before assumptions disable simplification.
        if (!m_sat->inconsistent())
            m_sat->simplify();
        m_dirty = false;
        return true;
    }

    lbool lit_value(sat::literal l) const {
        return m_sat->value(l);
    }

    bool learn(sat::literal_vector const& expl) {
        uint_set seen;
        sat::literal_vector cls;
        for (sat::literal l : expl) {
            if (l == sat::null_literal)
                continue;
            sat::literal n = ~l;
            if (seen.contains(n.index()))
                continue;
            if (seen.contains((~n).index())) {
                m_failed = true;
                return false;
            }
            seen.insert(n.index());
            cls.push_back(n);
        }
        if (cls.empty()) {
            m_failed = true;
            return false;
        }
        // Asserted, not redundant: simplify_clause keeps literals assigned
        // above level 0, and the falsified clause becomes the CDCL conflict.
        m_sat->mk_clause(cls.size(), cls.data(), sat::status::asserted());
        ++m_th_conflicts;
        return true;
    }

    sat::check_result theory_final() {
        if (theory_consistent())
            return sat::check_result::CR_DONE;
        if (m_failed || !m_sat->inconsistent() || m_th_conflicts > 100000)
            return sat::check_result::CR_GIVEUP;
        return sat::check_result::CR_CONTINUE;
    }

    void reset_uf() {
        for (unsigned i = 0; i < m_nodes.size(); ++i) {
            m_nodes[i].parent = i;
            m_nodes[i].class_has = m_nodes[i].is_cst;
            if (!m_nodes[i].is_cst)
                m_nodes[i].cst_node = UINT_MAX;
        }
        m_adj.reset();
        m_adj.resize(m_nodes.size());
    }

    unsigned find_str(unsigned x) {
        unsigned r = x;
        while (m_nodes[r].parent != r)
            r = m_nodes[r].parent;
        while (m_nodes[x].parent != r) {
            unsigned n = m_nodes[x].parent;
            m_nodes[x].parent = r;
            x = n;
        }
        return r;
    }

    // The equality graph, not the parent pointers, carries the explanation.
    // Linking roots with the original literal drops the path that justified
    // those roots and learns a clause that is too strong.
    bool explain_str(unsigned src, unsigned dst, sat::literal_vector& out) {
        if (src == dst)
            return true;
        svector<int> parent;
        parent.resize(m_nodes.size(), -1);
        svector<sat::literal> via;
        via.resize(m_nodes.size());
        unsigned_vector q;
        q.push_back(src);
        parent[src] = static_cast<int>(src);
        for (unsigned h = 0; h < q.size(); ++h) {
            unsigned u = q[h];
            if (u == dst)
                break;
            for (sedge const& e : m_adj[u]) {
                if (parent[e.n] != -1)
                    continue;
                parent[e.n] = static_cast<int>(u);
                via[e.n] = e.lit;
                q.push_back(e.n);
            }
        }
        if (parent[dst] == -1)
            return false;
        for (unsigned u = dst; u != src; u = static_cast<unsigned>(parent[u]))
            out.push_back(via[u]);
        return true;
    }

    bool unite_str(unsigned a, unsigned b, sat::literal lit, sat::literal_vector& expl) {
        m_adj[a].push_back(sedge{ b, lit });
        m_adj[b].push_back(sedge{ a, lit });
        unsigned ra = find_str(a);
        unsigned rb = find_str(b);
        if (ra == rb)
            return true;
        if (m_nodes[ra].class_has && m_nodes[rb].class_has && m_nodes[ra].cst != m_nodes[rb].cst) {
            if (!explain_str(m_nodes[ra].cst_node, m_nodes[rb].cst_node, expl))
                m_failed = true;
            return false;
        }
        m_nodes[rb].parent = ra;
        if (m_nodes[rb].class_has && !m_nodes[ra].class_has) {
            m_nodes[ra].class_has = true;
            m_nodes[ra].cst = m_nodes[rb].cst;
            m_nodes[ra].cst_node = m_nodes[rb].cst_node;
        }
        return true;
    }

    bool used_string(zstring const& s) const {
        for (zstring const& u : m_str_consts)
            if (u == s)
                return true;
        return false;
    }

    zstring fresh_string(unsigned root) {
        for (unsigned n = 0;; ++n) {
            zstring s(std::string("kconfirm-") + std::to_string(n));
            if (used_string(s))
                continue;
            m_str_consts.push_back(s);
            m_nodes[root].class_has = true;
            m_nodes[root].cst = s;
            return s;
        }
    }

    bool activate_int(unsigned i, bool pos) {
        if (!m_dl || m_int_on[i])
            return true;
        m_int_on[i] = 1;
        m_int_trail.push_back(i);
        iatom const& at = m_iatoms[i];
        sat::literal_vector expl;
        struct collect_expl {
            sat::literal_vector& out;
            void operator()(sat::literal const& l) { out.push_back(l); }
        };
        collect_expl grab{expl};
        edge_id id;
        if (pos)
            id = m_dl->add_edge(at.src, at.dst, at.w, at.lit);
        else {
            rational w(at.w);
            w.neg();
            w -= rational(1);
            id = m_dl->add_edge(at.dst, at.src, w, ~at.lit);
        }
        if (m_dl->enable_edge(id))
            return true;
        m_dl->traverse_neg_cycle(true, grab);
        learn(expl);
        return false;
    }

    void theory_asserted(sat::literal l) {
        if (!m_dl || m_sat->inconsistent() || l.var() >= m_int_of_var.size())
            return;
        int idx = m_int_of_var[l.var()];
        if (idx < 0)
            return;
        if (l != m_iatoms[idx].lit && l != ~m_iatoms[idx].lit)
            return;
        activate_int(static_cast<unsigned>(idx), l == m_iatoms[idx].lit);
    }

    void theory_push() {
        if (!m_dl)
            return;
        m_dl->push();
        m_int_lim.push_back(m_int_trail.size());
    }

    void theory_pop(unsigned n) {
        if (!m_dl || n == 0)
            return;
        m_dl->pop(n);
        unsigned lim = m_int_lim[m_int_lim.size() - n];
        for (unsigned i = m_int_trail.size(); i-- > lim; )
            m_int_on[m_int_trail[i]] = 0;
        m_int_trail.shrink(lim);
        m_int_lim.shrink(m_int_lim.size() - n);
    }

    void bound_ends(iatom const& at, bool pos, dl_var& s, dl_var& d, rational& w) const {
        if (pos) {
            s = at.src;
            d = at.dst;
            w = at.w;
            return;
        }
        s = at.dst;
        d = at.src;
        w = -at.w;
        w -= rational(1);
    }

    void add_bin(sat::literal a, sat::literal b) {
        sat::literal ls[2] = { a, b };
        add_clause(2, ls);
        ++m_local_clauses;
    }

    // Two opposite edges with negative total weight cannot both be selected.
    void compile_local_conflicts() {
        struct pol {
            unsigned idx;
            bool     pos;
            dl_var   s;
            dl_var   d;
            rational w;
        };
        std::map<uint64_t, vector<pol>> groups;
        for (unsigned i = 0; i < m_iatoms.size(); ++i) {
            for (unsigned p = 0; p < 2; ++p) {
                pol e;
                e.idx = i;
                e.pos = p != 0;
                bound_ends(m_iatoms[i], e.pos, e.s, e.d, e.w);
                if (e.s == e.d) {
                    if (e.w.is_neg()) {
                        sat::literal u = e.pos ? ~m_iatoms[i].lit : m_iatoms[i].lit;
                        m_sat->add_clause(u, sat::status::asserted());
                        ++m_local_clauses;
                    }
                    continue;
                }
                unsigned lo = static_cast<unsigned>(e.s < e.d ? e.s : e.d);
                unsigned hi = static_cast<unsigned>(e.s < e.d ? e.d : e.s);
                uint64_t key = (static_cast<uint64_t>(lo) << 32) | hi;
                groups[key].push_back(e);
            }
        }
        for (auto& group : groups) {
            vector<pol>& es = group.second;
            for (unsigned i = 0; i < es.size(); ++i) {
                for (unsigned j = i + 1; j < es.size(); ++j) {
                    if (es[i].idx == es[j].idx)
                        continue;
                    if (es[i].s != es[j].d || es[i].d != es[j].s)
                        continue;
                    if (!(es[i].w + es[j].w).is_neg())
                        continue;
                    sat::literal a = es[i].pos ? ~m_iatoms[es[i].idx].lit : m_iatoms[es[i].idx].lit;
                    sat::literal b = es[j].pos ? ~m_iatoms[es[j].idx].lit : m_iatoms[es[j].idx].lit;
                    add_bin(a, b);
                }
            }
        }

        // Three bounds around a cycle are rejected here too. Search was
        // spending hundreds of thousands of decisions rediscovering them.
        dl_var max_v = 0;
        for (auto& group : groups)
            for (pol const& e : group.second)
                max_v = std::max(max_v, std::max(e.s, e.d));
        vector<vector<pol>> out_edges;
        out_edges.resize(static_cast<unsigned>(max_v) + 1);
        for (auto& group : groups)
            for (pol const& e : group.second)
                out_edges[static_cast<unsigned>(e.s)].push_back(e);
        std::set<uint64_t> seen_tri;
        auto forbid = [&](pol const& e) {
            return e.pos ? ~m_iatoms[e.idx].lit : m_iatoms[e.idx].lit;
        };
        for (unsigned s = 0; s < out_edges.size(); ++s) {
            for (pol const& e1 : out_edges[s]) {
                for (pol const& e2 : out_edges[static_cast<unsigned>(e1.d)]) {
                    if (e1.idx == e2.idx || e2.d == e1.s)
                        continue;
                    for (pol const& e3 : out_edges[static_cast<unsigned>(e2.d)]) {
                        if (e3.d != e1.s || e3.idx == e1.idx || e3.idx == e2.idx)
                            continue;
                        if (!(e1.w + e2.w + e3.w).is_neg())
                            continue;
                        unsigned id[3] = {
                            e1.idx * 2 + (e1.pos ? 1u : 0u),
                            e2.idx * 2 + (e2.pos ? 1u : 0u),
                            e3.idx * 2 + (e3.pos ? 1u : 0u)
                        };
                        std::sort(id, id + 3);
                        uint64_t key = (static_cast<uint64_t>(id[0]) << 42) |
                                       (static_cast<uint64_t>(id[1]) << 21) |
                                       id[2];
                        if (!seen_tri.insert(key).second)
                            continue;
                        sat::literal ls[3] = { forbid(e1), forbid(e2), forbid(e3) };
                        add_clause(3, ls);
                        ++m_local_clauses;
                        if (m_local_clauses > 200000)
                            goto local_strings;
                    }
                }
            }
        }
        local_strings:

        std::map<unsigned, vector<std::pair<unsigned, sat::literal>>> by_var;
        for (unsigned i = 0; i < m_satoms.size(); ++i) {
            unsigned a = m_satoms[i].a;
            unsigned b = m_satoms[i].b;
            bool ac = m_nodes[a].is_cst;
            bool bc = m_nodes[b].is_cst;
            if (ac == bc)
                continue;
            unsigned var = ac ? b : a;
            unsigned cst = ac ? a : b;
            by_var[var].push_back(std::make_pair(cst, m_satoms[i].lit));
        }
        for (auto& group : by_var) {
            auto& es = group.second;
            for (unsigned i = 0; i < es.size(); ++i)
                for (unsigned j = i + 1; j < es.size(); ++j)
                    if (es[i].first != es[j].first)
                        add_bin(~es[i].second, ~es[j].second);
        }
        // s = t together with two different constants is one clause, so the
        // equality does not have to be discovered after the booleans are set.
        for (unsigned i = 0; i < m_satoms.size(); ++i) {
            unsigned a = m_satoms[i].a;
            unsigned b = m_satoms[i].b;
            if (m_nodes[a].is_cst || m_nodes[b].is_cst)
                continue;
            auto ia = by_var.find(a);
            auto ib = by_var.find(b);
            if (ia == by_var.end() || ib == by_var.end())
                continue;
            for (auto const& ca : ia->second)
                for (auto const& cb : ib->second)
                    if (ca.first != cb.first) {
                        sat::literal ls[3] = { ~m_satoms[i].lit, ~ca.second, ~cb.second };
                        add_clause(3, ls);
                        ++m_local_clauses;
                    }
        }
    }

    void init_dl() {
        if (m_iatoms.empty())
            return;
        m_dl = alloc(dl_graph<kc_ext>);
        m_dl->init_var(0);
        m_int_on.resize(m_iatoms.size(), 0);
        for (unsigned i = 0; i < m_iatoms.size(); ++i) {
            m_dl->init_var(m_iatoms[i].src);
            m_dl->init_var(m_iatoms[i].dst);
            sat::bool_var v = m_iatoms[i].lit.var();
            if (v >= m_int_of_var.size())
                m_int_of_var.resize(v + 1, -1);
            m_int_of_var[v] = static_cast<int>(i);
        }
        for (unsigned i = 0; i < m_sat->trail_size() && !m_sat->inconsistent(); ++i)
            theory_asserted(m_sat->trail_literal(i));
    }

    bool theory_consistent() {
        svector<lbool> ivals;
        ivals.resize(m_iatoms.size(), l_undef);
        svector<lbool> svals;
        svals.resize(m_satoms.size(), l_undef);
        for (unsigned i = 0; i < m_iatoms.size(); ++i)
            ivals[i] = lit_value(m_iatoms[i].lit);
        for (unsigned i = 0; i < m_satoms.size(); ++i)
            svals[i] = lit_value(m_satoms[i].lit);
        m_int_undef = 0;
        m_str_undef = 0;
        for (lbool v : ivals)
            if (v == l_undef)
                ++m_int_undef;
        for (lbool v : svals)
            if (v == l_undef)
                ++m_str_undef;

        if (m_dl) {
            for (unsigned i = 0; i < m_iatoms.size(); ++i) {
                if (ivals[i] == l_undef)
                    continue;
                if (!activate_int(i, ivals[i] == l_true))
                    return false;
            }
            rational zero = m_dl->get_assignment(0);
            m_model_int.reset();
            for (unsigned i = 0; i < m_int_exprs.size(); ++i) {
                dl_var v = static_cast<dl_var>(i + 1);
                rational val = m_dl->get_assignment(v);
                val -= zero;
                m_model_int.push_back(val);
            }
        }
        else {
            m_model_int.reset();
        }

        reset_uf();
        for (unsigned i = 0; i < m_satoms.size(); ++i) {
            if (svals[i] != l_true)
                continue;
            sat::literal_vector expl;
            if (!unite_str(m_satoms[i].a, m_satoms[i].b, m_satoms[i].lit, expl)) {
                learn(expl);
                return false;
            }
        }
        for (unsigned i = 0; i < m_satoms.size(); ++i) {
            if (svals[i] != l_false)
                continue;
            if (find_str(m_satoms[i].a) != find_str(m_satoms[i].b))
                continue;
            sat::literal_vector expl;
            if (m_satoms[i].a != m_satoms[i].b &&
                !explain_str(m_satoms[i].a, m_satoms[i].b, expl)) {
                m_failed = true;
                return false;
            }
            expl.push_back(~m_satoms[i].lit);
            learn(expl);
            return false;
        }
        m_model_str.reset();
        for (unsigned i = 0; i < m_str_exprs.size(); ++i) {
            unsigned root = find_str(m_str_ids[i]);
            if (!m_nodes[root].class_has)
                fresh_string(root);
            m_model_str.push_back(m_nodes[root].cst);
        }
        m_model_ready = true;
        return true;
    }

    void activate_fallback() {
        if (m_fb)
            return;
        ++m_fallback_n;
        if (m_fail)
            IF_VERBOSE(1, verbose_stream() << "(kconfirm \"fallback\" " << mk_bounded_pp(m_fail, m, 6) << ")\n";);
        m_fb = mk_smt_solver(m, m_params, symbol("ALL"));
        unsigned lim = 0;
        for (unsigned sz : m_limits) {
            for (; lim < sz; ++lim)
                m_fb->assert_expr(assertion_at(lim));
            m_fb->push();
        }
        for (; lim < m_assertions.size(); ++lim)
            m_fb->assert_expr(assertion_at(lim));
    }

public:
    kconfirm_solver(ast_manager& mgr, params_ref const& p):
        solver_na2as(mgr),
        m_params(p),
        m_assertions(mgr),
        m_pinned(mgr),
        m_arith(mgr),
        m_seq(mgr) {
    }

    ast_manager& get_manager() const override { return m; }

    ~kconfirm_solver() override {
        if (m_dl)
            dealloc(m_dl);
        if (m_sat)
            dealloc(m_sat);
    }

    solver* translate(ast_manager& dst, params_ref const& p) override {
        if (m_fb)
            return m_fb->translate(dst, p);
        ast_translation tr(m, dst);
        kconfirm_solver* r = alloc(kconfirm_solver, dst, p);
        unsigned lim = 0;
        for (unsigned sz : m_limits) {
            for (; lim < sz; ++lim)
                r->assert_expr(tr(assertion_at(lim)));
            r->push();
        }
        for (; lim < m_assertions.size(); ++lim)
            r->assert_expr(tr(assertion_at(lim)));
        return r;
    }

    void assert_expr_core(expr* t) override {
        if (m_fb) {
            m_fb->assert_expr(t);
            return;
        }
        m_assertions.push_back(t);
        m_dirty = true;
    }

    void push_core() override {
        if (m_fb) {
            m_fb->push();
            return;
        }
        m_limits.push_back(m_assertions.size());
        m_dirty = true;
    }

    void pop_core(unsigned n) override {
        if (m_fb) {
            m_fb->pop(n);
            return;
        }
        if (n == 0 || m_limits.empty())
            return;
        n = std::min(n, m_limits.size());
        unsigned sz = m_limits[m_limits.size() - n];
        m_assertions.shrink(sz);
        m_limits.shrink(m_limits.size() - n);
        m_dirty = true;
    }

    void set_progress_callback(progress_callback* cb) override {
        if (m_fb)
            m_fb->set_progress_callback(cb);
    }

    void set_phase(expr* e) override {
        if (m_fb)
            m_fb->set_phase(e);
    }
    void move_to_front(expr* e) override {
        if (m_fb)
            m_fb->move_to_front(e);
    }
    phase* get_phase() override { return m_fb ? m_fb->get_phase() : nullptr; }
    void set_phase(phase* p) override {
        if (m_fb)
            m_fb->set_phase(p);
    }

    expr_ref_vector cube(expr_ref_vector& vars, unsigned backtrack_level) override {
        if (m_fb)
            return m_fb->cube(vars, backtrack_level);
        return expr_ref_vector(m);
    }
    expr* congruence_root(expr* e) override { return m_fb ? m_fb->congruence_root(e) : e; }
    expr* congruence_next(expr* e) override { return m_fb ? m_fb->congruence_next(e) : nullptr; }
    expr_ref congruence_explain(expr* a, expr* b) override {
        if (m_fb)
            return m_fb->congruence_explain(a, b);
        return expr_ref(m.mk_eq(a, b), m);
    }
    expr_ref_vector get_trail(unsigned max_level) override {
        if (m_fb)
            return m_fb->get_trail(max_level);
        return expr_ref_vector(m);
    }
    void get_levels(ptr_vector<expr> const& vars, unsigned_vector& depth) override {
        if (m_fb)
            m_fb->get_levels(vars, depth);
    }

    unsigned get_num_assertions() const override {
        if (m_fb)
            return m_fb->get_num_assertions();
        return m_assertions.size();
    }
    expr* get_assertion(unsigned idx) const override {
        if (m_fb)
            return m_fb->get_assertion(idx);
        return m_assertions[idx];
    }

    lbool check_sat_core2(unsigned n, expr* const* assumptions) override {
        if (m_fb)
            return m_fb->check_sat(n, assumptions);
        if (!compile() || m_failed) {
            activate_fallback();
            return m_fb->check_sat(n, assumptions);
        }
        m_core_lits.reset();
        m_core_exprs.reset();
        sat::literal_vector al;
        for (unsigned i = 0; i < n; ++i) {
            sat::literal l = lit(assumptions[i]);
            if (m_failed)
                break;
            // Assumptions are units for this query. Elimination must not
            // treat their variables as gates it can delete or flip.
            m_sat->set_external(l.var());
            al.push_back(l);
            m_core_lits.push_back(l);
            m_core_exprs.push_back(assumptions[i]);
        }
        if (m_failed) {
            activate_fallback();
            return m_fb->check_sat(n, assumptions);
        }
        m_model_ready = false;
        lbool r = m_sat->check(al.size(), al.data());
        if (r == l_undef && (m_failed || m_th_conflicts > 100000)) {
            activate_fallback();
            return m_fb->check_sat(n, assumptions);
        }
        return r;
    }

    void collect_statistics_core(statistics& st) const override {
        if (m_fb)
            m_fb->collect_statistics(st);
        else if (m_sat)
            m_sat->collect_statistics(st);
        st.update("kconfirm.fallback", m_fallback_n);
        st.update("kconfirm.conflicts", m_th_conflicts);
        st.update("kconfirm.aliases", m_aliases);
        st.update("kconfirm.ladders", m_ladders);
        st.update("kconfirm.int-atoms", m_iatoms.size());
        st.update("kconfirm.int-undef", m_int_undef);
        st.update("kconfirm.str-atoms", m_satoms.size());
        st.update("kconfirm.str-undef", m_str_undef);
        st.update("kconfirm.local", m_local_clauses);
    }

    void get_unsat_core(expr_ref_vector& r) override {
        if (m_fb) {
            m_fb->get_unsat_core(r);
            return;
        }
        if (!m_sat)
            return;
        for (sat::literal c : m_sat->get_core()) {
            for (unsigned i = 0; i < m_core_lits.size(); ++i)
                if (m_core_lits[i] == c)
                    r.push_back(m_core_exprs[i]);
        }
    }

    void get_model_core(model_ref& out) override {
        if (m_fb) {
            m_fb->get_model(out);
            return;
        }
        model* md = alloc(model, m);
        out = md;
        if (!m_sat || !m_model_ready)
            return;
        for (unsigned i = 0; i < m_bools.size(); ++i) {
            lbool v = lit_value(m_bool_lits[i]);
            md->register_decl(to_app(m_bools[i])->get_decl(), v == l_false ? m.mk_false() : m.mk_true());
        }
        for (unsigned i = 0; i < m_int_exprs.size() && i < m_model_int.size(); ++i)
            md->register_decl(to_app(m_int_exprs[i])->get_decl(), m_arith.mk_numeral(m_model_int[i], true));
        for (unsigned i = 0; i < m_str_exprs.size() && i < m_model_str.size(); ++i)
            md->register_decl(to_app(m_str_exprs[i])->get_decl(), m_seq.str.mk_string(m_model_str[i]));
    }

    proof* get_proof_core() override { return m_fb ? m_fb->get_proof_core() : nullptr; }
    std::string reason_unknown() const override { return m_fb ? m_fb->reason_unknown() : m_unknown; }
    void set_reason_unknown(char const* msg) override {
        if (m_fb)
            m_fb->set_reason_unknown(msg);
        else if (msg)
            m_unknown = msg;
    }
    void get_labels(svector<symbol>& r) override {
        if (m_fb)
            m_fb->get_labels(r);
    }
};

sat::check_result kc_theory::check() {
    return m_owner.theory_final();
}

void kc_theory::asserted(sat::literal l) {
    m_owner.theory_asserted(l);
}

void kc_theory::push() {
    m_owner.theory_push();
}

void kc_theory::pop(unsigned n) {
    m_owner.theory_pop(n);
}

}

solver* mk_kconfirm_solver(ast_manager& m, params_ref const& p) {
    return alloc(kconfirm_solver, m, p);
}

tactic* mk_kconfirm_tactic(ast_manager& m, params_ref const& p) {
    tactic* t = mk_solver2tactic(mk_kconfirm_solver(m, p));
    t->set_display_name("kconfirm");
    return t;
}
