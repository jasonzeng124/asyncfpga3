module {
  func.func @memsum(%arg0: memref<32xi32> {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "n"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = arith.cmpi sgt, %arg1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1, ^bb3(%c0_i32 : i32) {handshake.name = "cond_br0"}
  ^bb1:  // pred: ^bb0
    %c1_i32 = arith.constant {handshake.name = "constant4"} 1 : i32
    %c31_i32 = arith.constant {handshake.name = "constant5"} 31 : i32
    %c-1_i32 = arith.constant {handshake.name = "constant6"} -1 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant7"} 0 : i32
    %1 = arith.addi %arg1, %c-1_i32 {handshake.name = "addi0"} : i32
    %2 = arith.minui %1, %c31_i32 {handshake.name = "minui0"} : i32
    %3 = arith.addi %2, %c1_i32 {handshake.name = "addi1"} : i32
    cf.br ^bb2(%c0_i32_0, %c0_i32_0 : i32, i32) {handshake.name = "br0"}
  ^bb2(%4: i32, %5: i32):  // 2 preds: ^bb1, ^bb2
    %c1_i32_1 = arith.constant {handshake.name = "constant8"} 1 : i32
    %6 = arith.extui %4 {handshake.name = "extui0"} : i32 to i64
    %7 = arith.index_cast %6 {handshake.name = "index_cast0"} : i64 to index
    %8 = memref.load %arg0[%7] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<32xi32>
    %9 = arith.addi %4, %c1_i32_1 {handshake.name = "addi2"} : i32
    %10 = arith.muli %8, %9 {handshake.name = "muli0"} : i32
    %11 = arith.addi %5, %10 {handshake.name = "addi3"} : i32
    %12 = arith.addi %4, %c1_i32_1 {handshake.name = "addi4"} : i32
    %13 = arith.cmpi ne, %12, %3 {handshake.name = "cmpi1"} : i32
    cf.cond_br %13, ^bb2(%12, %11 : i32, i32), ^bb3(%11 : i32) {handshake.name = "cond_br1"}
  ^bb3(%14: i32):  // 2 preds: ^bb0, ^bb2
    return {handshake.name = "return0"} %14 : i32
  }
}

