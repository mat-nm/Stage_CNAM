

allcoq: Makefile
	(cd coq_src && make)

alldoc: allcoq
	(cd coq_src && make alldoc)

coq_src/Makefile: coq_src/_CoqProject
	(cd coq_src && ../resources/build_make.sh)

clean:
	rm -rf pdf html *.v.d *.native *.cmi *.cmo *.cmx *.cmxs *.o *.glob */*.native */*.cmi */*.cmo */*.cmx */*.cmxs */*.o */*.glob
	(cd coq_src && make clean)

cleanall:
	cd coq_src; make clean
	rm -f *~ */*~ */*/*~
	rm -f .*~ */.*~ */*/.*~
	rm -rf auto */auto */*/auto
	rm -f *.log */*.log */*/*.log
	rm -f *.aux */*.aux */*/*.aux

cleandistribCARE:
	rm .git

include ./resources/MoreMakefile
