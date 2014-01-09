STDLIB_DIR=../../agda-stdlib
AD_DIR=../adapter
CONCURRENT_DIR=../concurrent-agda
SESSION_EXAMPLES_DIR=Session/Examples/
AGDA_IMPORTS=-i "$(STDLIB_DIR)/src" -i "$(AD_DIR)" -i "$(CONCURRENT_DIR)" -i "."

html : Session.lagda Session/Examples.lagda
	agda --html $(AGDA_IMPORTS) $<

Session/Examples/% : $(SESSION_EXAMPLES_DIR)/%.lagda
	agda -c --compile-dir=$(SESSION_EXAMPLES_DIR) \
                --ghc-flag="-threaded" --ghc-flag="-package concurrent-agda-ffi" \
		$(AGDA_IMPORTS) $<

examples :
	for i in `ls $(SESSION_EXAMPLES_DIR)/*.lagda | sed s/.lagda//`; do \
	 	make $$i; \
	done
