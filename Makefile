STDLIB_DIR=../../agda-stdlib
AD_DIR=../adapter
CONCURRENT_DIR=../concurrent-agda
SESSION_EXAMPLES_DIR=Session/Examples/
AGDA_IMPORTS=-i "$(STDLIB_DIR)/src" -i "$(AD_DIR)" -i "$(CONCURRENT_DIR)" -i "."
AGDA_ROOTS=Session.lagda Session/Examples.lagda

# TODO How to do this properly?
html : $(AGDA_ROOTS)
	for i in $(AGDA_ROOTS); do \
		agda --html $(AGDA_IMPORTS) $$i; \
	done

Session/Examples/% : $(SESSION_EXAMPLES_DIR)/%.lagda
	agda -c --compile-dir=$(SESSION_EXAMPLES_DIR)     \
                --ghc-flag="-threaded"                    \
		--ghc-flag="-package concurrent-agda-ffi" \
		$(AGDA_IMPORTS) $<

# TODO How to do this properly?
examples :
	for i in `ls $(SESSION_EXAMPLES_DIR)/*.lagda | sed s/.lagda//`; do \
	 	make $$i; \
	done
