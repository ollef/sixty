declare fastcc void @.$module_init()

define i32 @main() {
  call fastcc void @.$module_init()
  ret i32 0
}

