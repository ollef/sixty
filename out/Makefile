%.s: %.ll
	llc $^ -relocation-model=pic -o $@

%.exe: %.s
	clang $^ -o $@

%.opt.ll: %.ll
	opt $^ -o $@ -S -O3

%.opt.s: %.opt.ll
	llc $^ -relocation-model=pic -o $@ -O3
