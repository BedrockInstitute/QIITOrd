# SPDX-License-Identifier: AGPL-3.0-only
AGDA   ?= agda
PANDOC ?= pandoc
PERL   ?= perl
EVERYTHING := src/Everything.lagda.md
HTML_DIR   := _build/html
SITE_DIR   := _build/site

.PHONY: typecheck html site clean

# Type-check the whole development.
typecheck:
	$(AGDA) $(EVERYTHING)

# Run Agda's built-in HTML backend: literate (.lagda.md) modules become
# highlighted, cross-linked .md; plain .agda dependencies become .html.
html:
	$(AGDA) --html --html-highlight=auto --html-dir=$(HTML_DIR) $(EVERYTHING)

# Turn Agda's output into a browsable site: pandoc renders each .md to .html
# (keeping the highlighted <pre class="Agda"> blocks and their cross-references),
# the already-.html dependency pages and the CSS are copied over, and a landing
# page redirects to the umbrella module.
#
# Prose cross-links in the literate source are written as repo-relative paths
# (e.g. QIITOrd/Base.lagda.md) so they resolve in GitHub's file browser; on the
# flat rendered site the same module is QIITOrd.Base.html, so rewrite each prose
# link's .lagda.md/.agda target (slash → dot, suffix → .html). Agda's own code
# cross-references are emitted as raw HTML and already point at .html, so this
# markdown-link pass leaves them — and any absolute URLs — untouched.
site: html
	rm -rf $(SITE_DIR)
	mkdir -p $(SITE_DIR)
	cp $(HTML_DIR)/*.css  $(SITE_DIR)/ 2>/dev/null || true
	cp $(HTML_DIR)/*.html $(SITE_DIR)/ 2>/dev/null || true
	for f in $(HTML_DIR)/*.md; do \
	  base=$$(basename "$$f" .md); \
	  $(PANDOC) --standalone --metadata title="$$base" --css Agda.css "$$f" -o "$(SITE_DIR)/$$base.html"; \
	  $(PERL) -i -pe 's{href="(?!\w+://)([^"#]+)\.(?:lagda\.md|agda)(#[^"]*)?"}{my($$p,$$a)=($$1,$$2//"");$$p=~s!/!.!g;qq{href="$$p.html$$a"}}ge' "$(SITE_DIR)/$$base.html"; \
	done
	printf '<!doctype html>\n<meta charset="utf-8">\n<title>QIITOrd</title>\n<meta http-equiv="refresh" content="0; url=QIITOrd.html">\n<p><a href="QIITOrd.html">QIITOrd documentation</a></p>\n' > $(SITE_DIR)/index.html
	touch $(SITE_DIR)/.nojekyll
	@echo "Site built in $(SITE_DIR)"

clean:
	rm -rf _build
