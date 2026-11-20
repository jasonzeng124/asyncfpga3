module {
  func.func @share_test_2(%arg0: memref<100xi32> {handshake.arg_name = "a"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32) {handshake.name = "br0"}
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb1
    %c100_i32 = arith.constant {handshake.name = "constant18"} 100 : i32
    %c1_i32 = arith.constant {handshake.name = "constant19"} 1 : i32
    %c456784_i32 = arith.constant {handshake.name = "constant20"} 456784 : i32
    %c123456_i32 = arith.constant {handshake.name = "constant21"} 123456 : i32
    %c16_i32 = arith.constant {handshake.name = "constant22"} 16 : i32
    %c15_i32 = arith.constant {handshake.name = "constant23"} 15 : i32
    %c14_i32 = arith.constant {handshake.name = "constant24"} 14 : i32
    %c13_i32 = arith.constant {handshake.name = "constant25"} 13 : i32
    %c9_i32 = arith.constant {handshake.name = "constant26"} 9 : i32
    %c6_i32 = arith.constant {handshake.name = "constant27"} 6 : i32
    %c18_i32 = arith.constant {handshake.name = "constant28"} 18 : i32
    %c17_i32 = arith.constant {handshake.name = "constant29"} 17 : i32
    %c11_i32 = arith.constant {handshake.name = "constant30"} 11 : i32
    %c4_i32 = arith.constant {handshake.name = "constant31"} 4 : i32
    %c3_i32 = arith.constant {handshake.name = "constant32"} 3 : i32
    %c2_i32 = arith.constant {handshake.name = "constant33"} 2 : i32
    %2 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg0[%3] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<100xi32>
    %5 = arith.addi %1, %0 {handshake.name = "addi0"} : i32
    %6 = arith.addi %5, %c123456_i32 {handshake.name = "addi1"} : i32
    %7 = arith.muli %6, %0 {handshake.name = "muli0"} : i32
    %8 = arith.muli %7, %c456784_i32 {handshake.name = "muli1"} : i32
    %9 = arith.shli %4, %c6_i32 {handshake.name = "shli0"} : i32
    %10 = arith.shli %4, %c9_i32 {handshake.name = "shli1"} : i32
    %11 = arith.shli %4, %c13_i32 {handshake.name = "shli2"} : i32
    %12 = arith.addi %10, %11 {handshake.name = "addi5"} : i32
    %13 = arith.addi %9, %12 {handshake.name = "addi6"} : i32
    %14 = arith.shli %4, %c14_i32 {handshake.name = "shli3"} : i32
    %15 = arith.shli %4, %c15_i32 {handshake.name = "shli4"} : i32
    %16 = arith.shli %4, %c16_i32 {handshake.name = "shli5"} : i32
    %17 = arith.addi %15, %16 {handshake.name = "addi7"} : i32
    %18 = arith.addi %14, %17 {handshake.name = "addi8"} : i32
    %19 = arith.addi %13, %18 {handshake.name = "addi9"} : i32
    %20 = arith.muli %19, %0 {handshake.name = "muli3"} : i32
    %21 = arith.addi %8, %20 {handshake.name = "addi2"} : i32
    %22 = arith.shli %4, %c2_i32 {handshake.name = "shli6"} : i32
    %23 = arith.shli %4, %c3_i32 {handshake.name = "shli7"} : i32
    %24 = arith.addi %22, %23 {handshake.name = "addi10"} : i32
    %25 = arith.shli %4, %c4_i32 {handshake.name = "shli8"} : i32
    %26 = arith.shli %4, %c11_i32 {handshake.name = "shli9"} : i32
    %27 = arith.addi %25, %26 {handshake.name = "addi11"} : i32
    %28 = arith.addi %24, %27 {handshake.name = "addi12"} : i32
    %29 = arith.shli %4, %c14_i32 {handshake.name = "shli10"} : i32
    %30 = arith.shli %4, %c15_i32 {handshake.name = "shli11"} : i32
    %31 = arith.addi %29, %30 {handshake.name = "addi13"} : i32
    %32 = arith.shli %4, %c17_i32 {handshake.name = "shli12"} : i32
    %33 = arith.shli %4, %c18_i32 {handshake.name = "shli13"} : i32
    %34 = arith.addi %32, %33 {handshake.name = "addi14"} : i32
    %35 = arith.addi %31, %34 {handshake.name = "addi15"} : i32
    %36 = arith.addi %28, %35 {handshake.name = "addi16"} : i32
    %37 = arith.muli %36, %6 {handshake.name = "muli5"} : i32
    %38 = arith.addi %21, %37 {handshake.name = "addi3"} : i32
    %39 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %40 = arith.index_cast %39 {handshake.name = "index_cast1"} : i64 to index
    memref.store %38, %arg0[%40] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : memref<100xi32>
    %41 = arith.addi %0, %c1_i32 {handshake.name = "addi4"} : i32
    %42 = arith.cmpi ne, %41, %c100_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %42, ^bb1(%41, %6 : i32, i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    return {handshake.name = "return0"}
  }
}

