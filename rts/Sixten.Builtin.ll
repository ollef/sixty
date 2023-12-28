
declare void @print_int(i64 %i)
declare void @exit(i32)

@Sixten.Builtin.Int = unnamed_addr constant i64 u0x0000000800000000
@Sixten.Builtin.Type = unnamed_addr constant i64 u0x0000000800000000
@Sixten.Builtin.EmptyRepresentation = unnamed_addr constant i64 0
@Sixten.Builtin.PointerRepresentation = unnamed_addr constant i64 u0x0000000000000008
@Sixten.Builtin.WordRepresentation = unnamed_addr constant i64 u0x0000000800000000

define external fastcc void @Sixten.Builtin.unknown(ptr %destination, i64 %a) {
  call void @exit(i32 7411)
  unreachable
}

define external fastcc i64 @Sixten.Builtin.addRepresentation(i64 %a, i64 %b) {
  %result = add i64 %a, %b
  ret i64 %result
}

define external fastcc i64 @Sixten.Builtin.maxRepresentation(i64 %a, i64 %b) {
  %a_ptrs = trunc i64 %a to i32
  %b_ptrs = trunc i64 %b to i32
  %a_non_ptrs64 = lshr i64 %a, 32
  %b_non_ptrs64 = lshr i64 %b, 32
  %a_non_ptrs = trunc i64 %a_non_ptrs64 to i32
  %b_non_ptrs = trunc i64 %b_non_ptrs64 to i32
  %a_ptrs_lt_b_ptrs = icmp ult i32 %a_ptrs, %b_ptrs
  %result_ptrs = select i1 %a_ptrs_lt_b_ptrs, i32 %b_ptrs, i32 %a_ptrs
  %a_non_ptrs_lt_b_non_ptrs = icmp ult i32 %a_non_ptrs, %b_non_ptrs
  %result_non_ptrs = select i1 %a_non_ptrs_lt_b_non_ptrs, i32 %b_non_ptrs, i32 %a_non_ptrs
  %result_lower = zext i32 %result_ptrs to i64
  %result_non_ptrs64 = zext i32 %result_non_ptrs to i64
  %result_upper = shl nuw i64 %result_non_ptrs64, 32
  %result = or i64 %result_lower, %result_upper
  ret i64 %result
}

define external fastcc void @Sixten.Builtin.printInt(i64 %i) {
  call void @print_int(i64 %i)
}

define external fastcc i64 @Sixten.Builtin.addInt(i64 %a, i64 %b) {
  %result = add i64 %a, %b
  ret i64 %result
}

define external fastcc i64 @Sixten.Builtin.mulInt(i64 %a, i64 %b) {
  %result = mul i64 %a, %b
  ret i64 %result
}

define external fastcc i64 @Sixten.Builtin.subInt(i64 %a, i64 %b) {
  %result = sub i64 %a, %b
  ret i64 %result
}

define external fastcc i64 @Sixten.Builtin.representationBytes(i64 %a) {
  %ptr_bytes = call fastcc i64 @Sixten.Builtin.representationPointerBytes(i64 %a)
  %non_ptr_bytes = call fastcc i64 @Sixten.Builtin.representationNonPointerBytes(i64 %a)
  %bytes = add nuw i64 %ptr_bytes, %non_ptr_bytes
  ret i64 %bytes
}

define external fastcc i64 @Sixten.Builtin.representationPointerBytes(i64 %a) {
  %ptrs = trunc i64 %a to i32
  %ptrs64 = zext i32 %ptrs to i64
  ret i64 %ptrs64
}

define external fastcc i64 @Sixten.Builtin.representationNonPointerBytes(i64 %a) {
  %non_ptrs = lshr i64 %b, 32
  ret i64 %non_ptrs
}
