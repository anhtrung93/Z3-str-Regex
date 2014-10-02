#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<stdarg.h>
#include<memory.h>
#include<z3.h>

void exitf(const char* message) 
{
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}

void error_handler(Z3_context ctx, Z3_error_code e) 
{
    printf("Error code: %d\n", e);
    exitf("incorrect use of Z3");
}

Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err) 
{
    Z3_context ctx;
    
    Z3_set_param_value(cfg, "MODEL", "true");
    ctx = Z3_mk_context(cfg);
#ifdef TRACING
    Z3_trace_to_stderr(ctx);
#endif
    Z3_set_error_handler(ctx, err);
    
    return ctx;
}

Z3_context mk_context() 
{
    Z3_config  cfg;
    Z3_context ctx;
    cfg = Z3_mk_config();
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    return ctx;
}


Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty) 
{
    Z3_symbol   s  = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}

Z3_ast mk_bool_var(Z3_context ctx, const char * name) 
{
    Z3_sort ty = Z3_mk_bool_sort(ctx);
    return mk_var(ctx, name, ty);
}

Z3_ast mk_int_var(Z3_context ctx, const char * name) 
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return mk_var(ctx, name, ty);
}

Z3_ast mk_int(Z3_context ctx, int v) 
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return Z3_mk_int(ctx, v, ty);
}


Z3_ast mk_unary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x) 
{
    Z3_ast args[1] = {x};
    return Z3_mk_app(ctx, f, 1, args);
}

Z3_ast mk_binary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y) 
{
    Z3_ast args[2] = {x, y};
    return Z3_mk_app(ctx, f, 2, args);
}

void check(Z3_context ctx, Z3_lbool expected_result)
{
    Z3_model m      = 0;
    Z3_lbool result = Z3_check_and_get_model(ctx, &m);
    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");
        printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));
        break;
    case Z3_L_TRUE:
        printf("sat\n%s\n", Z3_model_to_string(ctx, m));
        break;
    }
    if (m) {
        Z3_del_model(ctx, m);
    }
    if (result != expected_result) {
        exitf("unexpected result");
    }
}

void display_eqc(Z3_theory t, Z3_ast n) {
    Z3_context c = Z3_theory_get_context(t);
    Z3_ast curr = n;
    printf("  ----- begin eqc of %s", Z3_ast_to_string(c, n));
    printf(", root: %s\n", Z3_ast_to_string(c, Z3_theory_get_eqc_root(t, n)));
    do {
        printf("  %s\n", Z3_ast_to_string(c, curr));
        curr = Z3_theory_get_eqc_next(t, curr);
    }
    while (curr != n);
    printf("  ----- end of eqc\n");
}

void display_eqc_parents(Z3_theory t, Z3_ast n) {
    Z3_context c = Z3_theory_get_context(t);
    Z3_ast curr = n;
    printf("  ----- begin eqc (theory) parents of %s\n", Z3_ast_to_string(c, n));
    do {
        unsigned num_parents = Z3_theory_get_num_parents(t, curr);
        unsigned i;
        for (i = 0; i < num_parents; i++) {
            Z3_ast p = Z3_theory_get_parent(t, curr, i);
            printf("  %s\n", Z3_ast_to_string(c, p));
        }
        curr = Z3_theory_get_eqc_next(t, curr);
    }
    while (curr != n);
    printf("  ----- end of eqc (theory) parents\n");
}

void display_new_eq(Z3_theory t, Z3_ast n1, Z3_ast n2) {
    printf("====== begin new equality\n");
    display_eqc(t, n1);
    display_eqc_parents(t, n1);
    printf("  ==\n");
    display_eqc(t, n2);
    display_eqc_parents(t, n2);
    printf("====== end new equality\n");
}

Z3_ast get_eqc_value(Z3_theory t, Z3_ast n) {
    Z3_ast curr = n;
    do {
        if (Z3_theory_is_value(t, curr))
            return curr;
        curr = Z3_theory_get_eqc_next(t, curr);
    }
    while (curr != n);
    return 0;
}


struct _SimpleTheoryData {
    Z3_sort      S; 
    Z3_func_decl f; 
    Z3_func_decl p; 
    Z3_ast       lunit; 
    Z3_ast       runit; 
};

typedef struct _SimpleTheoryData SimpleTheoryData;

void Th_delete(Z3_theory t) {
    SimpleTheoryData * td = (SimpleTheoryData *)Z3_theory_get_ext_data(t);
    printf("Delete\n");
    free(td);
}

Z3_bool Th_reduce_app(Z3_theory t, Z3_func_decl d, unsigned n, Z3_ast const args[], Z3_ast * result) {
    SimpleTheoryData * td = (SimpleTheoryData*)Z3_theory_get_ext_data(t);
    if (d == td->f) {
        if (args[0] == td->lunit) {
            *result = args[1];
            return Z3_TRUE;
        }
        else if (args[1] == td->runit) {
            *result = args[0];
            return Z3_TRUE;
        }
    }
    return Z3_FALSE; // failed to simplify
}

void Th_new_app(Z3_theory t, Z3_ast n) {
    Z3_context c = Z3_theory_get_context(t);
    printf("New app: %s\n", Z3_ast_to_string(c, n));
}

void Th_new_elem(Z3_theory t, Z3_ast n) {
    Z3_context c = Z3_theory_get_context(t);
    printf("New elem: %s\n", Z3_ast_to_string(c, n));
}

void Th_init_search(Z3_theory t) {
    printf("Starting search\n");
}

void Th_push(Z3_theory t) {
    printf("Push\n");
}

void Th_pop(Z3_theory t) {
    printf("Pop\n");
}

void Th_reset(Z3_theory t) {
    printf("Reset\n");
}

void Th_restart(Z3_theory t) {
    printf("Restart\n");
}

void apply_runit_axiom_for_parents_of(Z3_theory t, Z3_ast n) {
    SimpleTheoryData * td = (SimpleTheoryData*)Z3_theory_get_ext_data(t);
    Z3_context c = Z3_theory_get_context(t);
    /*
      The following idiom is the standard approach for traversing
      applications of the form
      
      g(..., n', ...) 
      where
      - g is an interpreted function symbol of \c t.
      - n' is in the same equivalence class of n.
    */
    Z3_ast n_prime = n;
    do {
        unsigned num_parents = Z3_theory_get_num_parents(t, n_prime);
        unsigned i;
        for (i = 0; i < num_parents; i++) {
            Z3_app parent = Z3_to_app(c, Z3_theory_get_parent(t, n_prime, i));
            /* check whether current parent if of the form f(a, n_prime) */
            if (Z3_get_app_decl(c, parent) == td->f && Z3_get_app_arg(c, parent, 1) == n_prime) {
                /* assert f(a, 1r) = a */
                Z3_ast a = Z3_get_app_arg(c, parent, 0);
                Z3_theory_assert_axiom(t, Z3_mk_eq(c, mk_binary_app(c, td->f, a, td->runit), a));
                /* Instead of asserting f(1l, a) = a, we could also have asserted
                   the clause:
                   (not (n_prime = 1r)) or (f(a, n_prime) = a)
                   
                   However, this solution is wasteful, because the axiom 
                   assert f(a, 1r) = a is simpler and more general.
                   Note that n_prime is in the equivalence class of n,
                   and n is now equal to 1l. So, n_prime is also equal to 1l.
                   Then, using congruence, Z3 will also deduce that f(n_prime, a) = a
                   using the simpler axiom.
                */
            }
        }
        n_prime = Z3_theory_get_eqc_next(t, n_prime);
    }
    while (n_prime != n);
}

void apply_lunit_axiom_for_parents_of(Z3_theory t, Z3_ast n) {
    SimpleTheoryData * td = (SimpleTheoryData*)Z3_theory_get_ext_data(t);
    Z3_context c = Z3_theory_get_context(t);
    Z3_ast n_prime = n;
    do {
        unsigned num_parents = Z3_theory_get_num_parents(t, n_prime);
        unsigned i;
        for (i = 0; i < num_parents; i++) {
            Z3_app parent = Z3_to_app(c, Z3_theory_get_parent(t, n_prime, i));
            /* check whether current parent if of the form f(n_prime, a) */
            if (Z3_get_app_decl(c, parent) == td->f && Z3_get_app_arg(c, parent, 0) == n_prime) {
                /* assert f(1l, a) = a */
                Z3_ast a = Z3_get_app_arg(c, parent, 1);
                Z3_theory_assert_axiom(t, Z3_mk_eq(c, mk_binary_app(c, td->f, td->lunit, a), a));
                /* see comments in apply_runit_axiom_for_parents_of */
            }
        }
        n_prime = Z3_theory_get_eqc_next(t, n_prime);
    }
    while (n_prime != n);
}

void Th_new_eq(Z3_theory t, Z3_ast n1, Z3_ast n2) {
    SimpleTheoryData * td = (SimpleTheoryData*)Z3_theory_get_ext_data(t);
    //Z3_context c = Z3_theory_get_context(t);
    display_new_eq(t, n1, n2);
    if (Z3_theory_get_eqc_root(t, n1) == Z3_theory_get_eqc_root(t, td->lunit)) {
        apply_lunit_axiom_for_parents_of(t, n2);
    }
    if (Z3_theory_get_eqc_root(t, n2) == Z3_theory_get_eqc_root(t, td->lunit)) {
        apply_lunit_axiom_for_parents_of(t, n1);
    }
    if (Z3_theory_get_eqc_root(t, n1) == Z3_theory_get_eqc_root(t, td->runit)) {
        apply_runit_axiom_for_parents_of(t, n2);
    }
    if (Z3_theory_get_eqc_root(t, n2) == Z3_theory_get_eqc_root(t, td->runit)) {
        apply_runit_axiom_for_parents_of(t, n1);
    }
}

void Th_new_diseq(Z3_theory t, Z3_ast n1, Z3_ast n2) {
    Z3_context c = Z3_theory_get_context(t);
    printf("New disequality: %s ", Z3_ast_to_string(c, n1));
    printf("!= %s\n", Z3_ast_to_string(c, n2));
}

void Th_new_relevant(Z3_theory t, Z3_ast n) {
    Z3_context c = Z3_theory_get_context(t);
    printf("Relevant: %s\n", Z3_ast_to_string(c, n));
}

void Th_new_assignment(Z3_theory t, Z3_ast n, Z3_bool v) {
    Z3_context c = Z3_theory_get_context(t);
    printf("Assigned: %s --> %d\n", Z3_ast_to_string(c, n), v);
}

Z3_bool Th_final_check(Z3_theory t) {
    printf("Final check\n");
    return Z3_TRUE;
}

Z3_theory mk_simple_theory(Z3_context ctx) {
    Z3_sort f_domain[2];
    Z3_symbol s_name      = Z3_mk_string_symbol(ctx, "S");
    Z3_symbol f_name      = Z3_mk_string_symbol(ctx, "f");
    Z3_symbol p_name      = Z3_mk_string_symbol(ctx, "p");
    Z3_symbol l_name      = Z3_mk_string_symbol(ctx, "l1");
    Z3_symbol r_name      = Z3_mk_string_symbol(ctx, "r1");
    Z3_sort B             = Z3_mk_bool_sort(ctx);
    SimpleTheoryData * td = (SimpleTheoryData*)malloc(sizeof(SimpleTheoryData));  
    Z3_theory Th          = Z3_mk_theory(ctx, "simple_th", td);
    td->S                 = Z3_theory_mk_sort(ctx, Th, s_name); 
    f_domain[0] = td->S; f_domain[1] = td->S;
    td->f                 = Z3_theory_mk_func_decl(ctx, Th, f_name, 2, f_domain, td->S);
    td->p                 = Z3_theory_mk_func_decl(ctx, Th, p_name, 1, &td->S, B); 
    /*
      Create 1r and 1l. They are created as theory values. Therefore,
      we have 1r != 1l for free.
    */
    td->lunit             = Z3_theory_mk_value(ctx, Th, l_name, td->S);
    td->runit             = Z3_theory_mk_value(ctx, Th, r_name, td->S);

    Z3_set_delete_callback(Th, Th_delete);
    Z3_set_reduce_app_callback(Th, Th_reduce_app);
    Z3_set_new_app_callback(Th, Th_new_app);
    Z3_set_new_elem_callback(Th, Th_new_elem);
    Z3_set_init_search_callback(Th, Th_init_search);
    Z3_set_push_callback(Th, Th_push);
    Z3_set_pop_callback(Th, Th_pop);
    Z3_set_reset_callback(Th, Th_reset);
    Z3_set_restart_callback(Th, Th_restart);
    Z3_set_new_eq_callback(Th, Th_new_eq);
    Z3_set_new_diseq_callback(Th, Th_new_diseq);
    Z3_set_new_relevant_callback(Th, Th_new_relevant);
    Z3_set_new_assignment_callback(Th, Th_new_assignment);
    Z3_set_final_check_callback(Th, Th_final_check);
    return Th;
}

void simple_example1() 
{
    Z3_ast a, b, c, f1, f2, f3, r, i;
    Z3_context ctx;
    Z3_theory Th;
    SimpleTheoryData * td;
    printf("\nsimple_example1\n");
    ctx = mk_context();
    Th = mk_simple_theory(ctx);
    td = (SimpleTheoryData*)Z3_theory_get_ext_data(Th);
    a  = mk_var(ctx, "a", td->S);
    b  = mk_var(ctx, "b", td->S);
    c  = mk_var(ctx, "c", td->S);
    i  = Z3_mk_ite(ctx, Z3_mk_eq(ctx, td->lunit, td->runit), c, td->runit);
    f1 = mk_binary_app(ctx, td->f, a, i);
    f2 = mk_binary_app(ctx, td->f, td->lunit, f1);
    f3 = mk_binary_app(ctx, td->f, b, f2);
    printf("%s\n==>\n", Z3_ast_to_string(ctx, f3));
    r  = Z3_simplify(ctx, f3);
    printf("%s\n",      Z3_ast_to_string(ctx, r));

    Z3_del_context(ctx);
}

void simple_example2() 
{
    Z3_ast a, b, c, d, f1;
    Z3_ast args[2];
    Z3_context ctx;
    Z3_theory Th;
    SimpleTheoryData * td;
    printf("\nsimple_example2\n");
    ctx = mk_context();
    Th = mk_simple_theory(ctx);
    td = (SimpleTheoryData*)Z3_theory_get_ext_data(Th);

    a  = mk_var(ctx, "a", td->S);
    b  = mk_var(ctx, "b", td->S);
    c  = mk_var(ctx, "c", td->S);
    d  = mk_var(ctx, "d", td->S);
    f1 = mk_binary_app(ctx, td->f, a, b);
    /* asserting a = c \/ b = d */
    args[0] = Z3_mk_eq(ctx, a, c);
    args[1] = Z3_mk_eq(ctx, b, d);
    Z3_assert_cnstr(ctx, Z3_mk_or(ctx, 2, args));
    /* asserting c = 1l */
    Z3_assert_cnstr(ctx, Z3_mk_eq(ctx, c, td->lunit));
    /* asserting d = 1r */
    Z3_assert_cnstr(ctx, Z3_mk_eq(ctx, d, td->runit));
    /* asserting b != f(a,b) */
    Z3_assert_cnstr(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, b, f1)));
    /* asserting a != f(a,b) */
    Z3_assert_cnstr(ctx, Z3_mk_not(ctx, Z3_mk_eq(ctx, a, f1)));
    /* asserting p(a) */
    Z3_assert_cnstr(ctx, mk_unary_app(ctx, td->p, a));
    /* asserting !p(b) */
    Z3_assert_cnstr(ctx, Z3_mk_not(ctx, mk_unary_app(ctx, td->p, b)));

    // printf("Context:\n%s\n", Z3_context_to_string(ctx));
    check(ctx, Z3_L_FALSE);
    Z3_del_context(ctx);
}


struct _PATheoryData {
    Z3_sort      String;
    Z3_func_decl Compare;
};

typedef struct _PATheoryData PATheoryData;

Z3_ast PATh_mk_string_value(Z3_theory t, char const * str) {
    Z3_context ctx      = Z3_theory_get_context(t);
    PATheoryData * td   = (PATheoryData *)Z3_theory_get_ext_data(t);
    /* store the string as the name of the new interpreted value */
    Z3_symbol str_sym   = Z3_mk_string_symbol(ctx, str);
    return Z3_theory_mk_value(ctx, t, str_sym, td->String);
}

void PATh_delete(Z3_theory t) {
    PATheoryData * td = (PATheoryData *)Z3_theory_get_ext_data(t);
    printf("Delete\n");
    free(td);
}

Z3_lbool Compare(Z3_theory t, Z3_ast n1, Z3_ast n2) {
    Z3_context ctx      = Z3_theory_get_context(t);
    printf("Compare(%s", Z3_ast_to_string(ctx, n1));
    printf(", %s)", Z3_ast_to_string(ctx, n2));
    if (Z3_theory_is_value(t, n1) && Z3_theory_is_value(t, n2)) {
        Z3_func_decl d1     = Z3_get_app_decl(ctx, Z3_to_app(ctx, n1));
        Z3_func_decl d2     = Z3_get_app_decl(ctx, Z3_to_app(ctx, n2));
        Z3_symbol    s1     = Z3_get_decl_name(ctx, d1);
        Z3_symbol    s2     = Z3_get_decl_name(ctx, d2);
        Z3_string    str1   = Z3_get_symbol_string(ctx, s1);
        Z3_string    str2;
        int strcmp_result;
        /* the next call to Z3_get_symbol_string will invalidate str1, so we need to create a copy */
        char * str1_copy    = strdup(str1);
        str2                = Z3_get_symbol_string(ctx, s2);
        strcmp_result       = strcmp(str1_copy, str2);
        free(str1_copy);
        if (strcmp_result == 0) {
            printf(" = true\n");
            return Z3_L_TRUE;
        }
        else {
            printf(" = false\n");
            return Z3_L_FALSE;
        }
    }
    printf(" = unknown\n");
    return Z3_L_UNDEF;
}

Z3_bool PATh_reduce_app(Z3_theory t, Z3_func_decl d, unsigned n, Z3_ast const args[], Z3_ast * result) {
    Z3_context ctx    = Z3_theory_get_context(t);
    PATheoryData * td = (PATheoryData*)Z3_theory_get_ext_data(t);
    if (d == td->Compare) {
        switch (Compare(t, args[0], args[1])) {
        case Z3_L_TRUE:
            *result = Z3_mk_true(ctx);
            return Z3_TRUE; 
        case Z3_L_FALSE:
            *result = Z3_mk_false(ctx);
            return Z3_TRUE;
        case Z3_L_UNDEF:
            return Z3_FALSE; // failed to simplify
        }
    }
    return Z3_FALSE; // failed to simplify
}

void apply_compare_axiom_for_parents_of(Z3_theory t, Z3_ast n, Z3_ast v) {
    PATheoryData * td = (PATheoryData*)Z3_theory_get_ext_data(t);
    Z3_context c = Z3_theory_get_context(t);
    Z3_ast n_prime = Z3_theory_get_eqc_root(t, n);
    do {
        unsigned num_parents = Z3_theory_get_num_parents(t, n_prime);
        unsigned i;
        for (i = 0; i < num_parents; i++) {
            Z3_app parent = Z3_to_app(c, Z3_theory_get_parent(t, n_prime, i));
            if (Z3_get_app_decl(c, parent) == td->Compare) {
                Z3_ast arg1 = Z3_get_app_arg(c, parent, 0);
                Z3_ast arg2 = Z3_get_app_arg(c, parent, 1);
                if (Z3_theory_get_eqc_root(t, arg1) == n)
                    arg1 = v;
                else
                    arg1 = get_eqc_value(t, arg1);
                if (Z3_theory_get_eqc_root(t, arg2) == n)
                    arg2 = v;
                else
                    arg2 = get_eqc_value(t, arg2);
                if (arg1 != 0 && arg2 != 0) {
                    switch (Compare(t, arg1, arg2)) {
                    case Z3_L_TRUE:
                        // assert axiom: Compare(arg1, arg2)
                        Z3_theory_assert_axiom(t, mk_binary_app(c, td->Compare, arg1, arg2));
                        break;
                    case Z3_L_FALSE:
                        // assert axiom: !Compare(arg1, arg2)
                        Z3_theory_assert_axiom(t, Z3_mk_not(c, mk_binary_app(c, td->Compare, arg1, arg2)));
                        break;
                    case Z3_L_UNDEF:
                        // do nothing
                        break; 
                    }
                }
            }
        }
        n_prime = Z3_theory_get_eqc_next(t, n_prime);
    }
    while (n_prime != n);
}

void PATh_new_eq(Z3_theory t, Z3_ast n1, Z3_ast n2) {
//    PATheoryData * td = (PATheoryData*)Z3_theory_get_ext_data(t);
//    Z3_context c = Z3_theory_get_context(t);
    Z3_ast v1 = get_eqc_value(t, n1);
    Z3_ast v2 = get_eqc_value(t, n2);
    display_new_eq(t, n1, n2);
    if (get_eqc_value(t, n1) != 0) {
        apply_compare_axiom_for_parents_of(t, n2, v1);
    }
    if (v2 != 0) {
        apply_compare_axiom_for_parents_of(t, n1, v2);
    }
}

Z3_bool PATh_final_check(Z3_theory t) {
    PATheoryData * td = (PATheoryData*)Z3_theory_get_ext_data(t);
    Z3_context c = Z3_theory_get_context(t);
    unsigned i, num;
    printf("Final check\n");
    /* check whether all (relevant) Compare(n1, n2) applications could be evaluated */
    num = Z3_theory_get_num_apps(t);
    for (i = 0; i < num; i++) {
        Z3_ast curr    = Z3_theory_get_app(t, i);
        Z3_func_decl d = Z3_get_app_decl(c, Z3_to_app(c, curr));
        if (d == td->Compare) {
            Z3_ast arg1 = Z3_get_app_arg(c, Z3_to_app(c, curr), 0);
            Z3_ast arg2 = Z3_get_app_arg(c, Z3_to_app(c, curr), 1);
            if (get_eqc_value(t, arg1) == 0 || get_eqc_value(t, arg2) == 0) {
                printf("failed to evaluate Compare(%s", Z3_ast_to_string(c, arg1));
                printf(", %s)\n", Z3_ast_to_string(c, arg2));
                return Z3_FALSE; /* giving up... could not evaluate this Compare application */
            }
        }
    }
    return Z3_TRUE;
}

Z3_theory mk_pa_theory(Z3_context ctx) {
    Z3_sort compare_domain[2];
    Z3_symbol string_name  = Z3_mk_string_symbol(ctx, "String");
    Z3_symbol compare_name = Z3_mk_string_symbol(ctx, "Compare");
    Z3_sort B              = Z3_mk_bool_sort(ctx);
    PATheoryData * td      = (PATheoryData *)malloc(sizeof(PATheoryData));
    Z3_theory Th           = Z3_mk_theory(ctx, "CompareProcedurealAttachment", td);
    td->String             = Z3_theory_mk_sort(ctx, Th, string_name); 
    compare_domain[0] = td->String; 
    compare_domain[1] = td->String;
    td->Compare            = Z3_theory_mk_func_decl(ctx, Th, compare_name, 2, compare_domain, B);

    Z3_set_delete_callback(Th, PATh_delete);
    Z3_set_reduce_app_callback(Th, PATh_reduce_app);
    Z3_set_new_eq_callback(Th, PATh_new_eq);
    Z3_set_final_check_callback(Th, PATh_final_check);
    return Th;
}

void pa_theory_example1() 
{
    Z3_ast hello, world, c, d, n, r;
    Z3_context ctx;
    Z3_theory Th;
    PATheoryData * td;
    printf("\nprocedural attachment example1\n");
    ctx = mk_context();
    Th = mk_pa_theory(ctx);
    td = (PATheoryData*)Z3_theory_get_ext_data(Th);
    hello = PATh_mk_string_value(Th, "hello");
    world = PATh_mk_string_value(Th, "world");
    c  = mk_var(ctx, "c", td->String);
    d  = mk_var(ctx, "d", td->String);
    n  = Z3_mk_ite(ctx, mk_binary_app(ctx, td->Compare, hello, world), c, d);
    printf("%s\n==>\n", Z3_ast_to_string(ctx, n));
    r  = Z3_simplify(ctx, n);
    printf("%s\n",      Z3_ast_to_string(ctx, r));
    Z3_del_context(ctx);
}


void pa_theory_example2(int assert_b_eq_hello) 
{
    Z3_ast hello, world, test, a, b;
    Z3_ast args[2];
    Z3_context ctx;
    Z3_theory Th;
    PATheoryData * td;
    printf("\nprocedural attachment example2\n");
    ctx = mk_context();
    Th = mk_pa_theory(ctx);
    td = (PATheoryData*)Z3_theory_get_ext_data(Th);
    hello = PATh_mk_string_value(Th, "hello");
    world = PATh_mk_string_value(Th, "world");
    test  = PATh_mk_string_value(Th, "test");
    a     = mk_var(ctx, "a", td->String);
    b     = mk_var(ctx, "b", td->String);
    /* assert a = world \/ a = test */
    args[0] = Z3_mk_eq(ctx, a, world);
    args[1] = Z3_mk_eq(ctx, a, test);
    Z3_assert_cnstr(ctx, Z3_mk_or(ctx, 2, args));
    if (assert_b_eq_hello != 0) {
        /* assert b = hello */
        Z3_assert_cnstr(ctx, Z3_mk_eq(ctx, b, hello));
    }
    /* assert Compare(a, b) */
    Z3_assert_cnstr(ctx, mk_binary_app(ctx, td->Compare, a, b));
    
    if (assert_b_eq_hello != 0) {
        check(ctx, Z3_L_FALSE);
    }
    else {
        /* when "b = hello" is not asserted, the theory solver will
           fail to evaluate Compare(a, b)  */
        check(ctx, Z3_L_UNDEF);
    }
    Z3_del_context(ctx);
}



int main() 
{
    //simple_example1(); 
    simple_example2();
    //pa_theory_example1();
    //pa_theory_example2(1); 
    //pa_theory_example2(0); 
    return 0;
}
