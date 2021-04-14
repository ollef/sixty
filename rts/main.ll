declare i8* @init_global_area()
declare fastcc void @.$module_init(i64*)

define i32 @main() {
  %global_area = call i8* @init_global_area()
  %global_area_i64ptr = bitcast i8* %global_area to i64*

  call fastcc void @.$module_init(i64* %global_area_i64ptr)
  ret i32 0
}

