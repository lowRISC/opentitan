_list: Makefile.build support/Build/ToGlobalMakefile.xsl

bin/.build/Makefile: bin/.build/Makefile.expanded
	mkdir -p $(dir $@)
	xsltproc --xinclude -o $@ support/Build/ToGlobalMakefile.xsl $<

bin/.build/Makefile.expanded: Makefile.build
	mkdir -p $(dir $@)
	xsltproc --xinclude -o $@ support/Build/ExpandProducts.xsl $<

-include bin/.build/Makefile

.PHONY: clean
clean:
	rm -rf bin/
