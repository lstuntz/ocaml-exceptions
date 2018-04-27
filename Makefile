ML_FILES := $(wildcard *.ml)
CMO_FILES := $(patsubst %.ml,%.cmo,$(ML_FILES))
CMO_BUILD_FILES := $(patsubst %,_build/%,$(CMO_FILES))

OCAMLBUILD := ocamlbuild -use-ocamlfind # -cflags -w,+a-4

.PHONY: build
build: $(CMO_BUILD_FILES)

.PHONY: clean
clean:
	rm -r _build

_build/%.cmo: %.ml
	$(OCAMLBUILD) $(patsubst %.ml,%.cmo,$<)

%: _build/%.cmo
	@ $(OCAMLBUILD) $@.byte
	@ ./$@.byte
	@ rm $@.byte
