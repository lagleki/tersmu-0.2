PAPPY=pappy/pappy/pappy
PAPPYOPTS=--2010 -e --monad
all: tersmu tersmuBot
tersmu: *.hs Lojban.hs Morphology.hs Pappy/Parse.hs
	ghc -o tersmu --make Main
tersmuBot: *.hs Lojban.hs Morphology.hs Pappy/Parse.hs
	#killall tersmuBot || true
	ghc -o tersmuBot --make tersmuBot.hs
${PAPPY}:
	# get my patched version of Chris Done's version of Bryan Ford's pappy
	darcs clone http://mbays.freeshell.org/pappy
	cd pappy/pappy && make
Pappy/Parse.hs:
	mkdir Pappy || true
	${PAPPY} --2010 --write-files
Lojban.hs: Lojban.pappy ${PAPPY}
	${PAPPY} ${PAPPYOPTS} Lojban.pappy
Morphology.hs: Morphology.pappy ${PAPPY}
	${PAPPY} ${PAPPYOPTS} Morphology.pappy
test: tersmu
	rlwrap ./tersmu
