
declare void @print_int(i64 %i)
declare void @exit(i32)

@Sixten.Builtin.Int =  unnamed_addr  constant i64 8
@Sixten.Builtin.Type =  unnamed_addr  constant i64 8
@Sixten.Builtin.EmptyRepresentation =  unnamed_addr  constant i64 0
@Sixten.Builtin.WordRepresentation =  unnamed_addr  constant i64 8

define external fastcc void @Sixten.Builtin.fail(i64* %shadow_stack, i64* %destination, i64 %a) {
  call void @exit(i32 7411)
  unreachable
}

define external fastcc i64 @Sixten.Builtin.addRepresentation(i64* %shadow_stack, i64 %a, i64 %b) {
  %result = add i64 %a, %b
  ret i64 %result
}

define external fastcc i64 @Sixten.Builtin.maxRepresentation(i64* %shadow_stack, i64 %a, i64 %b) {
  %a_lt_b = icmp ult i64 %a, %b
  %result = select i1 %a_lt_b, i64 %b, i64 %a
  ret i64 %result
}

define external fastcc void @Sixten.Builtin.printInt(i64* %shadow_stack, i64 %i) {
  call void @print_int(i64 %i)
  ret void
}

define external fastcc i64 @Sixten.Builtin.addInt(i64* %shadow_stack, i64 %a, i64 %b) {
  %result = add i64 %a, %b
  ret i64 %result
}

define external fastcc i64 @Sixten.Builtin.mulInt(i64* %shadow_stack, i64 %a, i64 %b) {
  %result = mul i64 %a, %b
  ret i64 %result
}

define external fastcc i64 @Sixten.Builtin.subInt(i64* %shadow_stack, i64 %a, i64 %b) {
  %result = sub i64 %a, %b
  ret i64 %result
}
