declare i8* @init_global_area()
declare { i8*, i8* } @init_garbage_collector();
declare fastcc void @.$module_init(i64*, i64*, i64*)

define i32 @main() {
  %global_area = call i8* @init_global_area()
  %global_area_i64ptr = bitcast i8* %global_area to i64*
  %gc_state = call { i8*, i8* } @init_garbage_collector()
  %heap_pointer = extractvalue { i8*, i8* } %gc_state, 0
  %heap_limit = extractvalue { i8*, i8* } %gc_state, 1
  %heap_pointer_i64ptr = bitcast i8* %heap_pointer to i64*
  %heap_limit_i64ptr = bitcast i8* %heap_limit to i64*

  call fastcc void @.$module_init(i64* %heap_pointer_i64ptr, i64* %heap_limit_i64ptr, i64* %global_area_i64ptr)
  ret i32 0
}

