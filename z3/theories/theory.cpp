#include "theory.h"

namespace z3{
	
	int theory::theories_len = -1;

	theory::theory(context & c):object(c){
		add_theory(this);
		
		Z3_set_delete_callback(m_theory, theory_delete);
		Z3_set_reduce_app_callback(m_theory, theory_reduce_app);
		Z3_set_reduce_eq_callback(m_theory, theory_reduce_eq);
		Z3_set_reduce_distinct_callback(m_theory, theory_reduce_distinct);
		Z3_set_new_app_callback(m_theory, theory_new_app);
		Z3_set_new_elem_callback(m_theory, theory_new_elem);
		Z3_set_new_eq_callback(m_theory, theory_new_eq);
		Z3_set_new_diseq_callback(m_theory, theory_new_diseq);
		Z3_set_new_assignment_callback(m_theory, theory_new_assignment);
		Z3_set_new_relevant_callback(m_theory, theory_new_relevant);
		Z3_set_final_check_callback(m_theory, theory_final_check);
		Z3_set_init_search_callback(m_theory, theory_init_search);
		Z3_set_push_callback(m_theory, theory_push);
		Z3_set_pop_callback(m_theory, theory_pop);
		Z3_set_reset_callback(m_theory, theory_reset);
		Z3_set_restart_callback(m_theory, theory_restart);
	}

	inline expr theory::value(symbol const & name, sort const & s) {
		Z3_ast r = Z3_theory_mk_value(*m_ctx, m_theory, name, s); 
		check_error(); 
		return expr(this->ctx(), r); 
	}
	inline expr theory::value(char const * name, sort const & s) { return value(this->ctx().str_symbol(name), s); }
	inline expr theory::constant(symbol const & name, sort const & s) {
		Z3_ast r = Z3_theory_mk_constant(*m_ctx, m_theory, name, s); 
		check_error(); 
		return expr(this->ctx(), r); 
	}
	inline expr theory::constant(char const * name, sort const & s) { return constant(this->ctx().str_symbol(name), s); }
	inline func_decl theory::function(symbol const & name, unsigned arity, sort const * domain, sort const & range) {
		array<Z3_sort> args(arity);
		for (unsigned i = 0; i < arity; i++) {
		    check_context(domain[i], range);
		    args[i] = domain[i];
		}
		Z3_func_decl f = Z3_theory_mk_func_decl(*m_ctx, m_theory, name, arity, args.ptr(), range);
		check_error();
		return func_decl(this->ctx(), f);
	}
	inline func_decl theory::function(char const * name, unsigned arity, sort const * domain, sort const & range) {
		return function(range.ctx().str_symbol(name), arity, domain, range);
	}


	inline void theory::assert_axiom(expr ax){
		Z3_theory_assert_axiom(m_theory, Z3_ast(ax));
		check_error();
	}
	inline void theory::enable_axiom_simplification(bool flag){
		Z3_theory_enable_axiom_simplification(m_theory, flag);
		check_error();
	}
	inline void theory::assume_equal(expr lhs, expr rhs){
		Z3_theory_assume_eq(m_theory, Z3_ast(lhs), Z3_ast(rhs));
		check_error();
	}
	inline expr theory::get_eqc_root(expr n){
		Z3_ast temp = Z3_theory_get_eqc_root(m_theory, Z3_ast(n));
		check_error();
		return expr(this->ctx(), temp);
	}
	inline expr theory::get_eqc_next(expr n){
		Z3_ast temp = Z3_theory_get_eqc_next(m_theory, Z3_ast(n));
		check_error();
		return expr(this->ctx(), temp);
	}
	inline unsigned theory::get_num_parents(expr n){
		unsigned temp = Z3_theory_get_num_parents(m_theory, Z3_ast(n));
		check_error();
		return temp;
	}
	inline expr theory::get_parent(expr n, unsigned i){
		Z3_ast temp = Z3_theory_get_parent(m_theory, Z3_ast(n), i);
		check_error();
		return expr(this->ctx(), temp);
	}
	inline unsigned theory::get_num_elems(){
		unsigned temp = Z3_theory_get_num_elems(m_theory);
		check_error();
		return temp;
	}
	inline expr theory::get_elem(unsigned i){
		Z3_ast temp = Z3_theory_get_elem(m_theory, i);
		check_error();
		return expr(this->ctx(), temp);
	}
	inline unsigned theory::get_num_apps(){
		unsigned temp = Z3_theory_get_num_apps(m_theory);
		check_error();
		return temp;
	}
	inline expr theory::get_app(unsigned i){
		Z3_ast temp = Z3_theory_get_app(m_theory, i);
		check_error();
		return expr(this->ctx(), temp);
	}
	inline bool theory::is_value(expr n){
		Z3_bool r = Z3_theory_is_value(m_theory, Z3_ast(n));
		check_error();
		return r != 0;
	}
	inline bool theory::is_function(func_decl dl){
		Z3_bool r = Z3_theory_is_decl(m_theory, func_decl(dl));
		check_error();
		return r != 0;
	}
}

int main(){
return 0;
}
