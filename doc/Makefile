ASCIIDOC=asciidoc
XSLTPROC=xsltproc
DBLATEX=dblatex

RM ?= rm -f
CP ?= cp
MV ?= mv
CAT ?= cat
GEN-DOCINFO=gen-docinfo.pl

ifndef PERL_PATH
	PERL_PATH = /usr/bin/perl
endif

ASCIIDOC_EXTRA += -a docinfo

SPEC_TXT=mor1kx.asciidoc
SPEC_HTML=$(patsubst %.asciidoc,%.html,$(SPEC_TXT))
SPEC_XML=$(patsubst %.asciidoc,%.xml,$(SPEC_TXT))
SPEC_PDF=$(patsubst %.asciidoc,%.pdf,$(SPEC_TXT))

SPEC_DOCINFO=$(patsubst %.asciidoc,%-docinfo.xml,$(SPEC_TXT))

ifneq ($(findstring $(MAKEFLAGS),s),s)
ifndef V
	QUIET_ASCIIDOC		= @echo '   ' ASCIIDOC $@;
	QUIET_XSLTPROC		= @echo '   ' XSLTPROC $@;
	QUIET_DBLATEX		= @echo '   ' DBLATEX $@;
	QUIET_GEN-DOCINFO	= @echo '   ' GEN-DOCINFO $@;
	export V
endif
endif

all: html

html: $(SPEC_HTML)
pdf: $(SPEC_PDF)

$(SPEC_DOCINFO): $(SPEC_TXT) $(GEN-DOCINFO)
	$(QUIET_GEN-DOCINFO)$(CAT) $< | \
	$(PERL_PATH) -ne 'if (/__vstart__/../__vend__/) {print unless /__v(start|end)__/}' | \
	$(PERL_PATH) $(GEN-DOCINFO) > $@

$(SPEC_XML): $(SPEC_TXT) $(SPEC_DOCINFO)
	$(QUIET_ASCIIDOC)$(ASCIIDOC) $(ASCIIDOC_EXTRA) -b docbook $<

XSLT = docbook.xsl
XSLTOPTS = --xinclude --stringparam html.stylesheet docbook-xsl.css \
	--stringparam  section.autolabel 1 \
	--stringparam  section.label.includes.component.label 1

$(SPEC_HTML): $(SPEC_XML)
	$(QUIET_XSLTPROC)$(RM) $@+ $@ && \
	$(XSLTPROC) $(XSLTOPTS) -o $@+ $(XSLT) $< && \
	$(MV) $@+ $@

DBLATEXOPTS = --param=doc.publisher.show=0

$(SPEC_PDF): $(SPEC_XML)
	$(QUIET_DBLATEX)$(RM) $@+ $@ && \
	$(DBLATEX) $(DBLATEXOPTS) -o $@+ \
	-p /etc/asciidoc/dblatex/asciidoc-dblatex.xsl \
	-s /etc/asciidoc/dblatex/asciidoc-dblatex.sty $< && \
	$(MV) $@+ $@

clean:
	$(RM) *.xml *.xml+ *.html *.html+
	$(RM) openrisc1200_spec.pdf+ openrisc1200_spec.txt+

.PHONY: all clean html
