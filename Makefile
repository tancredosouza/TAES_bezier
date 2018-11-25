clear:
	find . -type f -name '*.glob' -delete
	find . -type f -name '\.*.aux' -delete
	find . -type f -name '*.vo' -delete

primitives.vo: primitives.v
	coqc primitives.v

auxiliary.vo: auxiliary.v primitives.vo
	coqc auxiliary.v

bezier-functions/binomial.vo: bezier-functions/binomial.v auxiliary.vo primitives.vo
	coqc bezier-functions/binomial.v

bezier-functions/recursive.vo: bezier-functions/recursive.v auxiliary.vo primitives.vo
	coqc bezier-functions/recursive.v

bezier-functions/polynomial.vo: bezier-functions/polynomial.v auxiliary.vo primitives.vo
	coqc bezier-functions/polynomial.v

properties/fst_order_interpolation/fst_order_interpolation_binomial.vo: properties/fst_order_interpolation/fst_order_interpolation_binomial.v bezier-functions/binomial.vo
	coqc properties/fst_order_interpolation/fst_order_interpolation_binomial.v

properties/fst_order_interpolation/fst_order_interpolation_polynomial.vo: properties/fst_order_interpolation/fst_order_interpolation_polynomial.v bezier-functions/polynomial.vo
	coqc properties/fst_order_interpolation/fst_order_interpolation_polynomial.v

properties/fst_order_interpolation/fst_order_interpolation_recursive.vo: properties/fst_order_interpolation/fst_order_interpolation_recursive.v bezier-functions/recursive.vo
	coqc properties/fst_order_interpolation/fst_order_interpolation_recursive.v

properties/fst_order_eq/fst_order_eq_recursive_polynomial.vo: properties/fst_order_eq/fst_order_eq_recursive_polynomial.v properties/fst_order_interpolation/fst_order_interpolation_polynomial.vo properties/fst_order_interpolation/fst_order_interpolation_recursive.vo
	coqc properties/fst_order_eq/fst_order_eq_recursive_polynomial.v

properties/fst_order_eq/fst_order_eq_polynomial_binomial.vo: properties/fst_order_eq/fst_order_eq_polynomial_binomial.v bezier-functions/binomial.vo bezier-functions/polynomial.vo
	coqc properties/fst_order_eq/fst_order_eq_polynomial_binomial.v

properties/fst_order_eq/fst_order_eq_binomial_recursive.vo: properties/fst_order_eq/fst_order_eq_binomial_recursive.v bezier-functions/binomial.vo bezier-functions/recursive.vo
	coqc properties/fst_order_eq/fst_order_eq_binomial_recursive.v

properties/fst_order_symm/fst_order_symm_polynomial.vo: properties/fst_order_symm/fst_order_symm_polynomial.v bezier-functions/polynomial.vo auxiliary.vo
	coqc properties/fst_order_symm/fst_order_symm_polynomial.v

properties/fst_order_symm/fst_order_symm_binomial.vo: properties/fst_order_symm/fst_order_symm_binomial.v bezier-functions/binomial.vo auxiliary.vo
	coqc properties/fst_order_symm/fst_order_symm_binomial.v

properties/fst_order_symm/fst_order_symm_recursive.vo: properties/fst_order_symm/fst_order_symm_recursive.v bezier-functions/recursive.vo auxiliary.vo
	coqc properties/fst_order_symm/fst_order_symm_recursive.v

examples/equivalent_exs.vo: examples/equivalent_exs.v bezier-functions/binomial.vo bezier-functions/recursive.vo bezier-functions/polynomial.vo auxiliary.vo primitives.vo
	coqc examples/equivalent_exs.v