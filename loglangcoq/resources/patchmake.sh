#!/bin/bash

# For compatibility with other sed.
SEDOPT='--posix'
echo SEDOPT = $SEDOPT
# Take one argument: the makefile to patch (otherwise this script
# could not be called from anywhere)

# reintroducing this line + an include at the end of file
match='coq_makefile -f _CoqProject -o Makefile'
insert='#	..\/resources\/patchmake.sh Makefile'
file=$1

sed $SEDOPT -e "s/$match/$match\\
$insert/" $file  | sponge $file

echo sed $SEDOPT 2 file = $file...


# Remove lines between html: and validate: bute keep validate:
sed $SEDOPT -e '
/^html:/,/gallinahtml:/ {
    /gallinahtml:/ !d
}' $file | sponge $file

echo sed $SEDOPT 3 file = $file...

sed $SEDOPT -e '
/userinstall:/,/clean:/ {
    /clean:/ !d
}' $file | sponge $file

match='clean:'
insert='	rm -rf pdf html *.v.d *.native *.cmi *.cmo *.cmx *.cmxs *.o *.glob *\/*.native *\/*.cmi *\/*.cmo *\/*.cmx *\/*.cmxs *\/*.o *\/*.glob'

sed $SEDOPT -e "s/$match/&\\
\
$insert/" $file | sponge $file


# match='[a-z]*html: \$(GLOBFILES) \$(VFILES)'
# sed $SEDOPT -i -e "s/$match/OBSOLETE&/" $file

# match='[a-z]*\.p[a-z]*:'
# sed $SEDOPT -i -e "s/$match/OBSOLETE&/" $file

# match='uninstall[a-z_-]*:'
# sed $SEDOPT -i -e "s/$match/OBSOLETE&/" $file

# match='install[a-z_-]*:'
# sed $SEDOPT -i -e "s/$match/OBSOLETE&/" $file

printf '\n-include ../resources/MoreMakefile\n' >> $1


### Local Variables: 
### mode: sh
### End: 
