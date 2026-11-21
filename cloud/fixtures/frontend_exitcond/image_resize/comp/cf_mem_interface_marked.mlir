module {
  func.func @image_resize(%arg0: memref<900xi32> {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "c"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant8"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%3: i32):  // 2 preds: ^bb1, ^bb2
    %c30_i32 = arith.constant {handshake.name = "constant9"} 30 : i32
    %c1_i32 = arith.constant {handshake.name = "constant10"} 1 : i32
    %c4_i64 = arith.constant {handshake.name = "constant11"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant12"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant13"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant14"} 1 : i64
    %4 = arith.extui %3 {handshake.name = "extui2"} : i32 to i64
    %5 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %6 = arith.shli %1, %c2_i64 {handshake.name = "shli1"} : i64
    %7 = arith.addi %5, %6 {handshake.name = "addi4"} : i64
    %8 = arith.shli %1, %c3_i64 {handshake.name = "shli2"} : i64
    %9 = arith.shli %1, %c4_i64 {handshake.name = "shli3"} : i64
    %10 = arith.addi %8, %9 {handshake.name = "addi5"} : i64
    %11 = arith.addi %7, %10 {handshake.name = "addi6"} : i64
    %12 = arith.addi %11, %4 {handshake.name = "addi0"} : i64
    %13 = arith.index_cast %12 {handshake.name = "index_cast0"} : i64 to index
    %14 = memref.load %arg0[%13] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<900xi32>
    %15 = arith.subi %arg1, %14 {handshake.name = "subi0"} : i32
    %16 = arith.extui %3 {handshake.name = "extui3"} : i32 to i64
    %17 = arith.shli %2, %c1_i64 {handshake.name = "shli4"} : i64
    %18 = arith.shli %2, %c2_i64 {handshake.name = "shli5"} : i64
    %19 = arith.addi %17, %18 {handshake.name = "addi7"} : i64
    %20 = arith.shli %2, %c3_i64 {handshake.name = "shli6"} : i64
    %21 = arith.shli %2, %c4_i64 {handshake.name = "shli7"} : i64
    %22 = arith.addi %20, %21 {handshake.name = "addi8"} : i64
    %23 = arith.addi %19, %22 {handshake.name = "addi9"} : i64
    %24 = arith.addi %23, %16 {handshake.name = "addi1"} : i64
    %25 = arith.index_cast %24 {handshake.name = "index_cast1"} : i64 to index
    memref.store %15, %arg0[%25] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : memref<900xi32>
    %26 = arith.addi %3, %c1_i32 {handshake.name = "addi2"} : i32
    %27 = arith.cmpi ne, %26, %c30_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %27, ^bb2(%26 : i32), ^bb3 {handshake.name = "cond_br0"}
  ^bb3:  // pred: ^bb2
    %c30_i32_1 = arith.constant {handshake.name = "constant15"} 30 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant16"} 1 : i32
    %28 = arith.addi %0, %c1_i32_2 {handshake.name = "addi3"} : i32
    %29 = arith.cmpi ne, %28, %c30_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %29, ^bb1(%28 : i32), ^bb4 {handshake.name = "cond_br1"}
  ^bb4:  // pred: ^bb3
    return {handshake.name = "return0"}
  }
}

