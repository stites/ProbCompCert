
# This is a development Makefile.
# It is meant to be used by developers who wish to modify the parser and messages.

# inspired by cparser/GNUMakefile, minus the de-lexer
# and https://gitlab.inria.fr/fpottier/menhir/-/blob/master/demos/calc-syntax-errors/Makefile.messages.maintenance

include ../Makefile.menhir

# Be more verbose about the automaton.

FLAGS    := $(MENHIR_FLAGS) -v -la 2

# So, here is our basic Menhir command.

COMMAND  := $(MENHIR) --coq Sparser.vy $(FLAGS)

# And this is the database of messages.

DATABASE := parser.messages

.PHONY: nothing correct complete update strip

nothing:
	@ echo "If you wish to compile ProbCompCert, please run \"make\" one level up."
	@ echo "If you wish to work on the Stan parser, please read Makefile"

# Checking correctness and irredundancy is done via --compile-errors.
# This entry is also called from [Makefile.extr] to compile the message
# database down to OCaml code.
# This also produces a description of the automaton in Sparser.automaton
# and a description of the conflicts (if any) in Sparser.conflicts.
correct:
	@ $(COMMAND) --compile-errors $(DATABASE) > Smessages.ml && \
	    echo "OK. The set of erroneous inputs is correct and irredundant."

# Checking completeness is done by first generating a complete list of
# erroneous sentences (in $(DATABASE)), then comparing the two
# .messages files for inclusion.
complete:
# Re-generate the list of error messages. This takes time (about 25 seconds).
	@ $(COMMAND) --list-errors >generated.messages
	@ echo "Number of error sentences that involve spurious reductions:"
	@ grep WARNING generated.messages | wc -l
# Check $(DATABASE) for completeness.
# We assume pre_parser.messages is up-to-date.
	@ $(COMMAND) --compare-errors generated.messages --compare-errors $(DATABASE) && \
	    echo "OK. The set of erroneous inputs is complete."
	@ rm -f generated.messages

update:
# Update the auto-comments in $(DATABASE).
	@ mv -f $(DATABASE) $(DATABASE).bak
	@ if ! $(COMMAND) --update-errors $(DATABASE).bak > $(DATABASE) ; then \
	  cp $(DATABASE).bak $(DATABASE) ; \
	fi
	@ echo "The auto-generated comments in $(DATABASE) have been re-generated."

# remove the automated comments in $(DATABASE)
strip:
	@ sed -e "/^##/d" -i.bak $(DATABASE)
	@ echo "Removing auto-generated comments in $(DATABASE)\nRegenerate with 'make update'."

# clean temp files
clean::
	rm -f *.bak generated.messages Sparser.automaton Sparser.conflicts 
