OTT_FILES  = ./*.ott

coq: $(OTT_FILES)
	ott -i $(OTT_FILES) -o ../coq/syntax_ott.v -coq_lngen true
	make METALIB.FIX_$(SYNTAX)_ott
	@if grep '<<no parses (' $@ >/dev/null 2>&1 && \
	[ -z "$(DONTSTOP)" ]; then \
	echo; \
	echo "***** OTT PARSE ERROR(S) *****"; \
	grep -n '<<no parses (' $@; \
	$(RM) $@; \
	exit 1; \
	fi >&2

latex: $(OTT_FILES)
	ott -tex_wrap false  -i $(OTT_FILES) -o ott-rules.tex
