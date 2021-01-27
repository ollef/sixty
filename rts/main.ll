declare i8* @init_stack()
declare i8* @init_global_area()
declare cc 10 void @.$module_init(i64*, i64*)

define i32 @main() {
  %stack = call i8* @init_stack()
  %stack_int = ptrtoint i8* %stack to i64
  %global_area = call i8* @init_global_area()
  %global_area_i64ptr = bitcast i8* %global_area to i64*

  %stack2_int = sub i64 %stack_int, 8
  %stack2 = inttoptr i64 %stack2_int to i64*
  %cont_int = ptrtoint void (i64*, i64*)* @main_cont to i64
  store i64 %cont_int, i64* %stack2, align 8

  call ghccc void @.$module_init(i64* %stack2, i64* %global_area_i64ptr)
  ret i32 0
}

define ghccc void @main_cont(i64* %stack, i64* %global_area) {
  ret void
}
