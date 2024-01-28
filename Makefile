all: build
.PHONY: all

build:
	@cargo build
.PHONY: build

clear:
	@cargo clear
	@$(RM) **/*.{aux,log,out,nav,snm,toc,vrb}
.PHONY: clear
