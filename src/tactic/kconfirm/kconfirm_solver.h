/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    kconfirm_solver.h

Abstract:

    Opt-in solver for the quantifier-free Boolean fragment with difference
    bounds and string equality. Boolean structure is compiled onto the SAT
    solver. Integer and string constraints are checked on a finished candidate.

--*/
#pragma once

#include "util/params.h"
#include "tactic/tactic.h"

class solver;
class ast_manager;

solver* mk_kconfirm_solver(ast_manager& m, params_ref const& p);
tactic* mk_kconfirm_tactic(ast_manager& m, params_ref const& p);

Z3_ADD_TACTIC(kconfirm_tactic, "kconfirm", "compile Boolean definitions to SAT, then check difference bounds and string equality.", mk_kconfirm_tactic(m, p));
