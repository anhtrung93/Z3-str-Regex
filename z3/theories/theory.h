#include "z3++.h"
#include <vector>

using namespace std;
using namespace z3;

namespace z3{
class theory : public object{
	public:
		Z3_theory m_theory;
		int m_id;

		const static int MAX_NUM_THEORIES = 5;
		static int theories_len;
		static theory* btn[MAX_NUM_THEORIES];
		
		static void add_theory(theory* th){
			++ theories_len;
			if (theories_len >= MAX_NUM_THEORIES){
				return;
			}
			btn[theories_len] = th;
			th->m_id = theories_len;
		};

		static void remove_theory(theory* th){
			int id = th->m_id;
			if (id < 0 || id > theories_len){
				return;
			}
			btn[id] = btn[theories_len];
			-- theories_len;
			btn[id]->m_id = id;
		};

		//Callback list
		static void theory_delete(Z3_theory th){get_theory(th)->delete_callback();}
		static Z3_bool theory_reduce_app(Z3_theory th, Z3_func_decl d, unsigned n, Z3_ast const args[], Z3_ast * result){
			theory * temp = get_theory(th);
			func_decl function = func_decl(temp->ctx(), d);
			vector<ast> ast_args;
			for (unsigned i = 0; i < n; ++i){
				ast_args.push_back(ast(temp->ctx(), args[i]));
			}
			ast result_ast = ast(temp->ctx(), *result);
			bool bool_val =	temp->reduce_app_callback(function, n, ast_args, result_ast);
			*result = Z3_ast(result_ast);
			return bool_val;
		}
		static Z3_bool theory_reduce_eq(Z3_theory th, Z3_ast s1, Z3_ast s2, Z3_ast * r) {
			theory * temp = get_theory(th);
			expr l_expr = expr(temp->ctx(), s1);
			expr r_expr = expr(temp->ctx(), s2);
			expr result_expr = expr(temp->ctx(), *r);
			bool bool_val = temp->reduce_eq_callback(l_expr, r_expr, result_expr);
			*r = Z3_ast(result_expr);
			return bool_val;
		}
		static Z3_bool theory_reduce_distinct(Z3_theory th, unsigned n, Z3_ast const args[], Z3_ast * result){
			theory * temp = get_theory(th);
			vector<ast> ast_args;
			for (unsigned i = 0; i < n; ++i){
				ast_args.push_back(ast(temp->ctx(), args[i]));
			}
			ast result_ast = ast(temp->ctx(), *result);
			bool bool_val =	temp->reduce_distinct_callback(n, ast_args, result_ast);
			*result = Z3_ast(result_ast);
			return bool_val;
		}	
		static void theory_new_app(Z3_theory th, Z3_ast n){
			theory * temp = get_theory(th);
			temp->new_app_callback(ast(temp->ctx(), n));
		}
		static void theory_new_elem(Z3_theory th, Z3_ast n){
			theory * temp = get_theory(th);
			temp->new_elem_callback(ast(temp->ctx(), n));
		}
		static void theory_new_eq(Z3_theory th, Z3_ast ast1, Z3_ast ast2){
			theory * temp = get_theory(th);
			temp->new_eq_callback(ast(temp->ctx(), ast1), ast(temp->ctx(), ast2));
		}
		static void theory_new_diseq(Z3_theory th, Z3_ast ast1, Z3_ast ast2){
			theory * temp = get_theory(th);
			temp->new_diseq_callback(ast(temp->ctx(), ast1), ast(temp->ctx(), ast2));
		}
		static void theory_new_assignment(Z3_theory th, Z3_ast n, Z3_bool v){
			theory * temp = get_theory(th);
			temp->new_assignment_callback(ast(temp->ctx(), n), v != 0);
		}
		static void theory_new_relevant(Z3_theory th, Z3_ast n){
			theory * temp = get_theory(th);
			temp->new_relevant_callback(ast(temp->ctx(), n));
		}
		static Z3_bool theory_final_check(Z3_theory th){
			return get_theory(th)->final_check_callback();
		}
		static void theory_init_search(Z3_theory th){
			get_theory(th)->init_search_callback();
		}
		static void theory_push(Z3_theory th){
			get_theory(th)->push_callback();
		}
		static void theory_pop(Z3_theory th){
			get_theory(th)->pop_callback();
		}
		static void theory_reset(Z3_theory th){
			get_theory(th)->reset_callback();
		}
		static void theory_restart(Z3_theory th){
			get_theory(th)->restart_callback();
		}
	
	public:
		static theory * get_theory(Z3_theory th){
			for (int id = 0; id <= theories_len; ++ id){
				if (btn[id]->m_theory == th){
					return btn[id];
				}
			}
			return NULL;
		};

		theory(context & c);
		//theory(context & c, Z3_theory th):object(c), m_theory(th) {theory::add_theory(this);}
		theory(theory const & th):object(th), m_theory(th.m_theory), m_id(th.m_id) {}
		~theory(){theory::remove_theory(this);}
		operator Z3_theory() const { return m_theory; }
		theory & operator=(theory const & s) { m_ctx = s.m_ctx; m_theory = s.m_theory; return *this; }

		//sort sort(symbol const & name);
		//sort sort(char const * name);
		expr value(symbol const & name, sort const & s);
		expr value(char const * name, sort const & s);
		expr constant(symbol const & name, sort const & s);
		expr constant(char const * name, sort const & s);
		func_decl function(symbol const & name, unsigned arity, sort const * domain, sort const & range);
		func_decl function(char const * name, unsigned arity, sort const * domain, sort const & range);


		void assert_axiom(expr ax);
		void assume_equal(expr lhs, expr rhs);
		void enable_axiom_simplification(bool flag);
		expr get_eqc_root(expr n);
		expr get_eqc_next(expr n);
		unsigned get_num_parents(expr n);
		expr get_parent(expr n, unsigned i);
		unsigned get_num_elems();
		expr get_elem(unsigned i);
		unsigned get_num_apps();
		expr get_app(unsigned i);
		bool is_value(expr n);
		bool is_function(func_decl dl);


		//Callback list to override
		void delete_callback(){}
		bool reduce_app_callback(func_decl function, unsigned arity, vector<ast> args, ast & result){return false;}
		bool reduce_eq_callback(expr l_expr, expr r_expr, expr & result_expr){return false;}
		bool reduce_distinct_callback(unsigned arity, vector<ast> args, ast & result){return false;}
		void new_app_callback(ast n){}
		void new_elem_callback(ast n){}
		void new_eq_callback(ast n1, ast n2){}
		void new_diseq_callback(ast n1, ast n2){}
		void new_assignment_callback(ast n, bool v){}
		void new_relevant_callback(ast n){}
		bool final_check_callback(){return true;}
		void init_search_callback(){}
		void push_callback(){}
		void pop_callback(){}
		void reset_callback(){}
		void restart_callback(){}
	};

}
