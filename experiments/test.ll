@.str = private unnamed_addr constant [13 x i8] c"hello world\0A\00"
@.stack_size = private unnamed_addr constant i64 2048
declare i32 @puts(i8* nocapture) nounwind
declare i8* @calloc(i64, i64)
declare void @free(i8*)
declare i32 @printf(i8*, ...)

@formatString = private constant [4 x i8] c"%d\0a\00" 

 ;define "cc 10" void @print_hello_world(i8* %stack_ptr) align 8 {
 ;  %cast210 = getelementptr [13 x i8], [13 x i8]* @.str, i64 0, i64 0
 ;  call i32 @puts(i8* %cast210)
 ;  ret void
 ;}
 ;
 ;define "cc 10" void @f(i8* %stack_ptr) align 8 {
 ;  %stack_ptr_i = ptrtoint i8* %stack_ptr to i64
 ;  %stack_ptr_2_i = add nuw i64 %stack_ptr_i, 8
 ;  %stack_ptr_2 = inttoptr i64 %stack_ptr_2_i to i8*
 ;  %stack_ptr_2_fptr = bitcast i8* %stack_ptr_2 to void (i8*)**
 ;  store void (i8*)* @print_hello_world, void (i8*)** %stack_ptr_2_fptr
 ;  tail call "cc 10" void @g(i8* %stack_ptr_2)
 ;  ret void
 ;}
 ;
 ;define "cc 10" void @g(i8* %stack_ptr) align 8 {
 ;  ret void
 ;}
 ;
 ;define i32 @main() {
 ;  %stack_size = load i64, i64* @.stack_size
 ;  %stack_ptr = call i8* @malloc(i64 %stack_size)
 ;  call "cc 10" void @print_hello_world(i8* %stack_ptr)
 ;  call void @free(i8* %stack_ptr)
 ;  ret i32 0
 ;}

define void @print_i64(i64 %number) {
  %result = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @formatString , i32 0, i32 0), i64 %number)
  ret void
}

define i32 @main() {
  %stack_size = load i64, i64* @.stack_size
  %stack_ptr = call i8* @calloc(i64 %stack_size, i64 8)
  call "cc 10" void @print_length(i8* %stack_ptr, i64 1000)
  call void @free(i8* %stack_ptr)
  ret i32 0
}

define private "cc 10" void @print_length(i8* %stack_ptr, i64 %arg) align 8 {
  %stack_ptr_i = ptrtoint i8* %stack_ptr to i64
  %stack_ptr_2_i = add nuw i64 %stack_ptr_i, 8
  %stack_ptr_2 = inttoptr i64 %stack_ptr_2_i to i8*
  %stack_ptr_2_fptr = bitcast i8* %stack_ptr_2 to void (i8*, i64)**
  store void (i8*, i64)* @print_result, void (i8*, i64)** %stack_ptr_2_fptr
  tail call void @length(i8* %stack_ptr_2, i64 %arg)
  ret void
}

define private "cc 10" void @print_result(i8* %stack_ptr, i64 %result) align 8 {
  call void @print_i64(i64 %result)
  %stack_ptr_i = ptrtoint i8* %stack_ptr to i64
  %stack_ptr_2_i = sub nuw i64 %stack_ptr_i, 8
  %stack_ptr_2 = inttoptr i64 %stack_ptr_2_i to i8*
  ret void
}

define "cc 10" void @length(i8* %stack_ptr, i64 %i) align 8 {
  %stack_ptr_i = ptrtoint i8* %stack_ptr to i64
  switch i64 %i, label %non-zero [ i64 0, label %zero ]
zero:
  %stack_ptr_fptr = bitcast i8* %stack_ptr to void (i8*, i64)**
  %cont = load void (i8*, i64)*, void (i8*, i64)** %stack_ptr_fptr
  tail call "cc 10" void %cont(i8* %stack_ptr, i64 0)
  ret void
non-zero:
  %stack_ptr_3_i = add nuw i64 %stack_ptr_i, 8
  %stack_ptr_3 = inttoptr i64 %stack_ptr_3_i to i8*
  %stack_ptr_3_fptr = bitcast i8* %stack_ptr_3 to void (i8*, i64)**
  store void (i8*, i64)* @length_1, void (i8*, i64)** %stack_ptr_3_fptr
  %i_2 = sub nuw i64 %i, 1
  tail call "cc 10" void @length(i8* %stack_ptr_3, i64 %i_2)
  ret void
}

define private "cc 10" void @length_1(i8* %stack_ptr, i64 %result) align 8 {
  ; call void @print_i64(i64 %result)
  %stack_ptr_i = ptrtoint i8* %stack_ptr to i64
  %stack_ptr_2_i = sub nuw i64 %stack_ptr_i, 8
  %stack_ptr_2 = inttoptr i64 %stack_ptr_2_i to i8*
  %stack_ptr_2_fptr = bitcast i8* %stack_ptr_2 to void (i8*, i64)**
  %cont = load void (i8*, i64)*, void (i8*, i64)** %stack_ptr_2_fptr
  %result_2 = add nuw i64 %result, 1
  tail call "cc 10" void %cont(i8* %stack_ptr_2, i64 %result_2)
  ret void
}
