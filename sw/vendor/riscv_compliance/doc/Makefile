# Makefile for RISC-V Compliance Task Group documentation

# This file is part of the RISC-V Foundation Compliance Task Group compliance
# tool set and documentation.

# Copyright (C) 2017 CodaSip Limited <www.codasip.com>
# Copyright (C) 2018 Embecosm Limited <www.embecosm.com>.
# Copyright (C) 2018 Imperas Limited <www.imperas.com>

# All rights reserved.

# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:

# 1. Redistributions of source code must retain the above copyright notice,
#    this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in the
#    documentation and/or other materials provided with the distribution.
# 3. Neither the name of mosquitto nor the names of its
#    contributors may be used to endorse or promote products derived from
#    this software without specific prior written permission.

# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
# LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
# CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.

# SPDX-License-Identifier: BSD-3-Clause

ROOT = README
SRC = $(ROOT).adoc
SRC_STRIPPED = $(ROOT)-stripped.adoc

.PHONY: all
all: pdf html

.PHONY: pdf
pdf: $(ROOT).pdf

$(ROOT).pdf: sanity-check $(SRC)
	asciidoctor-pdf -d article $(SRC)

.PHONY: html
html: $(ROOT).html

$(ROOT).html: sanity-check $(SRC)
	asciidoctor -d article -b html $(SRC)

# It is all too easy for the document history and title page to have diverging
# version numbers.  This target checks first.

.PHONY: sanity-check
sanity-check:
	@s=$$(sed -n < $(SRC) -e '3s/Issue //p') ; \
	t=$$(sed -n < $(SRC) -e "/== Document history/,/^$$/p" | \
	           grep -c "$${s}") ; \
	if [ $${t} -ne 1 ] ; \
	then \
	    echo "Version number of title and document history do not match" ; \
	    exit 1 ; \
	fi

custom.dict: custom.wordlist
	aspell --lang=en create master ./$@ < $<

.PHONY: spell
spell: custom.dict $(SRC)
	sed < $(SRC) > $(SRC_STRIPPED) -e 's/`[^`]\+`//gp' -e '/^----$$/,/^----$$/d'
	aspell --master=en_US --mode=none --add-extra-dicts=./custom.dict \
	    -c $(SRC_STRIPPED)
	$(RM) $(SRC_STRIPPED)

clean:
	rm -f $(ROOT)-stripped.adoc $(ROOT).pdf $(ROOT).html custom.dict
