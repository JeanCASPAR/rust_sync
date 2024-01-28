all: build
.PHONY: all

build:
	@cargo build
.PHONY: build

clean:
	@cargo clean
	@$(RM) **/*.{aux,log,out,nav,snm,toc,vrb}
.PHONY: clean
