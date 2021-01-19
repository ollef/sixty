
@Sixten.Builtin.Int =  unnamed_addr  constant i64 8
@Sixten.Builtin.Type =  unnamed_addr  constant i64 8
@Sixten.Builtin.EmptyRepresentation =  unnamed_addr  constant i64 0

define external ghccc void @Sixten.Bultin.addRepresentation(i64* %stack, i64* %a, i64* %b) {
  block:
    %a_int = ptrtoint i64* %a to i64
    %b_int = ptrtoint i64* %b to i64
    %result = add i64 %a_int, %b_int
    %result_pointer = inttoptr i64 %result to i64*

    %continuation = load i64, i64* %stack, align 8
    %continuation_pointer = inttoptr i64 %continuation to void (i64*, i64*)*
    store i64 undef, i64* %stack, align 8

    %stack_integer = ptrtoint i64* %stack to i64
    %stack2 = add i64 %stack_integer, 8
    %stack2_pointer = inttoptr i64 %stack2 to i64*
    tail call ghccc void %continuation_pointer(i64* %stack2_pointer, i64* %result_pointer)
    ret void
}

define external cc 10 void @Sixten.Bultin.maxRepresentation(i64* %stack, i64* %a, i64* %b) {
  block:
    %a_int = ptrtoint i64* %a to i64
    %b_int = ptrtoint i64* %b to i64
    %a_lt_b = icmp ult i64 %a_int, %b_int
    %result_pointer = select i1 %a_lt_b, i64* %b, i64* %a

    %continuation = load i64, i64* %stack, align 8
    %continuation_pointer = inttoptr i64 %continuation to void (i64*, i64*)*
    store i64 undef, i64* %stack, align 8

    %stack_integer = ptrtoint i64* %stack to i64
    %stack2 = add i64 %stack_integer, 8
    %stack2_pointer = inttoptr i64 %stack2 to i64*
    tail call ghccc void %continuation_pointer(i64* %stack2_pointer, i64* %result_pointer)
    ret void
}
