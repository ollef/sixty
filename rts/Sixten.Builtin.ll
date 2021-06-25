
declare void @print_int(i64 %i)
declare void @exit(i32)

@Sixten.Builtin.Int =  unnamed_addr  constant i64 8
@Sixten.Builtin.Type =  unnamed_addr  constant i64 8
@Sixten.Builtin.EmptyRepresentation =  unnamed_addr  constant i64 0
@Sixten.Builtin.WordRepresentation =  unnamed_addr  constant i64 8

define external fastcc { i64*, i64* } @Sixten.Builtin.fail(i64* %shadow_stack, i64* %heap_pointer, i64* %heap_limit, i64* %destination, i64 %a) {
  call void @exit(i32 7411)
  unreachable
}

define external fastcc { i64, i64*, i64* } @Sixten.Builtin.addRepresentation(i64* %shadow_stack, i64* %heap_pointer, i64* %heap_limit, i64 %a, i64 %b) {
  %result = add i64 %a, %b
  %result_with_heap_pointer_and_limit1 = insertvalue { i64, i64*, i64* } undef, i64 %result, 0
  %result_with_heap_pointer_and_limit2 = insertvalue { i64, i64*, i64* } %result_with_heap_pointer_and_limit1, i64* %heap_pointer, 1
  %result_with_heap_pointer_and_limit3 = insertvalue { i64, i64*, i64* } %result_with_heap_pointer_and_limit2, i64* %heap_limit, 2
  ret { i64, i64*, i64* } %result_with_heap_pointer_and_limit3
}

define external fastcc { i64, i64*, i64* } @Sixten.Builtin.maxRepresentation(i64* %shadow_stack, i64* %heap_pointer, i64* %heap_limit, i64 %a, i64 %b) {
  %a_lt_b = icmp ult i64 %a, %b
  %result = select i1 %a_lt_b, i64 %b, i64 %a
  %result_with_heap_pointer_and_limit1 = insertvalue { i64, i64*, i64* } undef, i64 %result, 0
  %result_with_heap_pointer_and_limit2 = insertvalue { i64, i64*, i64* } %result_with_heap_pointer_and_limit1, i64* %heap_pointer, 1
  %result_with_heap_pointer_and_limit3 = insertvalue { i64, i64*, i64* } %result_with_heap_pointer_and_limit2, i64* %heap_limit, 2
  ret { i64, i64*, i64* } %result_with_heap_pointer_and_limit3
}

define external fastcc { i64*, i64* } @Sixten.Builtin.printInt(i64* %shadow_stack, i64* %heap_pointer, i64* %heap_limit, i64 %tagged_i) {
  %i = ashr i64 %tagged_i, 1
  call void @print_int(i64 %i)
  %result_with_heap_pointer_and_limit1 = insertvalue { i64*, i64* } undef, i64* %heap_pointer, 0
  %result_with_heap_pointer_and_limit2 = insertvalue { i64*, i64* } %result_with_heap_pointer_and_limit1, i64* %heap_limit, 1
  ret { i64*, i64* } %result_with_heap_pointer_and_limit2
}

define external fastcc { i64, i64*, i64* } @Sixten.Builtin.addInt(i64* %shadow_stack, i64* %heap_pointer, i64* %heap_limit, i64 %a, i64 %b) {
  %result = add i64 %a, %b
  %result_with_heap_pointer_and_limit1 = insertvalue { i64, i64*, i64* } undef, i64 %result, 0
  %result_with_heap_pointer_and_limit2 = insertvalue { i64, i64*, i64* } %result_with_heap_pointer_and_limit1, i64* %heap_pointer, 1
  %result_with_heap_pointer_and_limit3 = insertvalue { i64, i64*, i64* } %result_with_heap_pointer_and_limit2, i64* %heap_limit, 2
  ret { i64, i64*, i64* } %result_with_heap_pointer_and_limit3
}

define external fastcc { i64, i64*, i64* } @Sixten.Builtin.mulInt(i64* %shadow_stack, i64* %heap_pointer, i64* %heap_limit, i64 %a, i64 %b) {
  %doubled_result = mul i64 %a, %b
  %result = ashr i64 %doubled_result, 1
  %result_with_heap_pointer_and_limit1 = insertvalue { i64, i64*, i64* } undef, i64 %result, 0
  %result_with_heap_pointer_and_limit2 = insertvalue { i64, i64*, i64* } %result_with_heap_pointer_and_limit1, i64* %heap_pointer, 1
  %result_with_heap_pointer_and_limit3 = insertvalue { i64, i64*, i64* } %result_with_heap_pointer_and_limit2, i64* %heap_limit, 2
  ret { i64, i64*, i64* } %result_with_heap_pointer_and_limit3
}

define external fastcc { i64, i64*, i64* }  @Sixten.Builtin.subInt(i64* %shadow_stack, i64* %heap_pointer, i64* %heap_limit, i64 %a, i64 %b) {
  %result = sub i64 %a, %b
  %result_with_heap_pointer_and_limit1 = insertvalue { i64, i64*, i64* } undef, i64 %result, 0
  %result_with_heap_pointer_and_limit2 = insertvalue { i64, i64*, i64* } %result_with_heap_pointer_and_limit1, i64* %heap_pointer, 1
  %result_with_heap_pointer_and_limit3 = insertvalue { i64, i64*, i64* } %result_with_heap_pointer_and_limit2, i64* %heap_limit, 2
  ret { i64, i64*, i64* } %result_with_heap_pointer_and_limit3
}
