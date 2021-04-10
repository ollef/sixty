
declare void @print_int(i64 %i)
declare void @exit(i32)

@Sixten.Builtin.Int =  unnamed_addr  constant i64 8
@Sixten.Builtin.Type =  unnamed_addr  constant i64 8
@Sixten.Builtin.EmptyRepresentation =  unnamed_addr  constant i64 0
@Sixten.Builtin.WordRepresentation =  unnamed_addr  constant i64 8

define external fastcc i64* @Sixten.Builtin.fail(i64* %a) {
  call void @exit(i32 7411)
  unreachable
}

define external fastcc i64* @Sixten.Builtin.addRepresentation(i64* %a, i64* %b) {
  block:
    %a_int = ptrtoint i64* %a to i64
    %b_int = ptrtoint i64* %b to i64
    %result = add i64 %a_int, %b_int
    %result_pointer = inttoptr i64 %result to i64*
    ret i64* %result_pointer
}

define external fastcc i64* @Sixten.Builtin.maxRepresentation(i64* %a, i64* %b) {
  block:
    %a_int = ptrtoint i64* %a to i64
    %b_int = ptrtoint i64* %b to i64
    %a_lt_b = icmp ult i64 %a_int, %b_int
    %result_pointer = select i1 %a_lt_b, i64* %b, i64* %a
    ret i64* %result_pointer
}

define external fastcc void @Sixten.Builtin.printInt(i64* %i) {
  block:
    %i_int = ptrtoint i64* %i to i64
    call void @print_int(i64 %i_int)
    ret void
}
