src_files=$(shell find . -name "*.hs")
test_files=$(shell find ../examples -name "*.box")

executable: ${src_files}
	ghc --make Main.hs

tests: executable ${test_files}
	./Main ${test_files}

# this is hTags as defined in agda's repo
TAGS: ${src_files}
	hTags -I. -eTAGS ${src_files}
