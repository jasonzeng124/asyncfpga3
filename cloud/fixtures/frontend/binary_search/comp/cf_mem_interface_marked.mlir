module {
  func.func @binary_search(%arg0: i32 {handshake.arg_name = "search"}, %arg1: memref<101xi32> {handshake.arg_name = "a"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb2
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg1[%2] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<101xi32>
    %4 = arith.cmpi eq, %3, %arg0 {handshake.name = "cmpi0"} : i32
    cf.cond_br %4, ^bb3(%0 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    %c-1_i32 = arith.constant {handshake.name = "constant5"} -1 : i32
    %c101_i32 = arith.constant {handshake.name = "constant6"} 101 : i32
    %c2_i32 = arith.constant {handshake.name = "constant7"} 2 : i32
    %5 = arith.addi %0, %c2_i32 {handshake.name = "addi0"} : i32
    %6 = arith.cmpi ult, %5, %c101_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %6, ^bb1(%5 : i32), ^bb3(%c-1_i32 : i32) {handshake.name = "cond_br1"}
  ^bb3(%7: i32):  // 2 preds: ^bb1, ^bb2
    %c1_i32 = arith.constant {handshake.name = "constant8"} 1 : i32
    cf.br ^bb4(%c1_i32 : i32) {handshake.name = "br1"}
  ^bb4(%8: i32):  // 2 preds: ^bb3, ^bb5
    %9 = arith.extui %8 {handshake.name = "extui1"} : i32 to i64
    %10 = arith.index_cast %9 {handshake.name = "index_cast1"} : i64 to index
    %11 = memref.load %arg1[%10] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<101xi32>
    %12 = arith.cmpi eq, %11, %arg0 {handshake.name = "cmpi2"} : i32
    cf.cond_br %12, ^bb6(%8 : i32), ^bb5 {handshake.name = "cond_br2"}
  ^bb5:  // pred: ^bb4
    %c-1_i32_0 = arith.constant {handshake.name = "constant9"} -1 : i32
    %c101_i32_1 = arith.constant {handshake.name = "constant10"} 101 : i32
    %c2_i32_2 = arith.constant {handshake.name = "constant11"} 2 : i32
    %13 = arith.addi %8, %c2_i32_2 {handshake.name = "addi1"} : i32
    %14 = arith.cmpi ult, %13, %c101_i32_1 {handshake.name = "cmpi3"} : i32
    cf.cond_br %14, ^bb4(%13 : i32), ^bb6(%c-1_i32_0 : i32) {handshake.name = "cond_br3"}
  ^bb6(%15: i32):  // 2 preds: ^bb4, ^bb5
    %c-1_i32_3 = arith.constant {handshake.name = "constant12"} -1 : i32
    %16 = arith.cmpi eq, %7, %c-1_i32_3 {handshake.name = "cmpi4"} : i32
    %17 = arith.select %16, %15, %7 {handshake.name = "select1"} : i32
    return {handshake.name = "return0"} %17 : i32
  }
}

