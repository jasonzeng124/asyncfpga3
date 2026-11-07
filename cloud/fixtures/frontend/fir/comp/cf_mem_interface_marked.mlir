module {
  func.func @fir(%arg0: memref<1000xi32> {handshake.arg_name = "di"}, %arg1: memref<1000xi32> {handshake.arg_name = "idx"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32) {handshake.name = "br0"}
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb1
    %c1000_i32 = arith.constant {handshake.name = "constant4"} 1000 : i32
    %c1_i32 = arith.constant {handshake.name = "constant5"} 1 : i32
    %c999_i32 = arith.constant {handshake.name = "constant6"} 999 : i32
    %2 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg1[%3] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<1000xi32>
    %5 = arith.subi %c999_i32, %0 {handshake.name = "subi0"} : i32
    %6 = arith.extui %5 {handshake.name = "extui1"} : i32 to i64
    %7 = arith.index_cast %6 {handshake.name = "index_cast1"} : i64 to index
    %8 = memref.load %arg0[%7] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<1000xi32>
    %9 = arith.muli %4, %8 {handshake.name = "muli0"} : i32
    %10 = arith.addi %1, %9 {handshake.name = "addi0"} : i32
    %11 = arith.addi %0, %c1_i32 {handshake.name = "addi1"} : i32
    %12 = arith.cmpi ult, %11, %c1000_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %12, ^bb1(%11, %10 : i32, i32), ^bb2(%10 : i32) {handshake.name = "cond_br0"}
  ^bb2(%13: i32):  // pred: ^bb1
    return {handshake.name = "return0"} %13 : i32
  }
}

