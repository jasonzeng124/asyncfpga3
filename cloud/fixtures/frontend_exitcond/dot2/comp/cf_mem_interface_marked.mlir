module {
  func.func @dot2(%arg0: memref<32xi32> {handshake.arg_name = "a"}, %arg1: memref<32xi32> {handshake.arg_name = "b"}, %arg2: i32 {handshake.arg_name = "n"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = arith.cmpi sgt, %arg2, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1, ^bb3(%c0_i32 : i32) {handshake.name = "cond_br0"}
  ^bb1:  // pred: ^bb0
    %c1_i32 = arith.constant {handshake.name = "constant4"} 1 : i32
    %c31_i32 = arith.constant {handshake.name = "constant5"} 31 : i32
    %c-1_i32 = arith.constant {handshake.name = "constant6"} -1 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant7"} 0 : i32
    %1 = arith.addi %arg2, %c-1_i32 {handshake.name = "addi0"} : i32
    %2 = arith.minui %1, %c31_i32 {handshake.name = "minui0"} : i32
    %3 = arith.addi %2, %c1_i32 {handshake.name = "addi1"} : i32
    cf.br ^bb2(%c0_i32_0, %c0_i32_0 : i32, i32) {handshake.name = "br0"}
  ^bb2(%4: i32, %5: i32):  // 2 preds: ^bb1, ^bb2
    %c1_i32_1 = arith.constant {handshake.name = "constant8"} 1 : i32
    %6 = arith.extui %4 {handshake.name = "extui0"} : i32 to i64
    %7 = arith.index_cast %6 {handshake.name = "index_cast0"} : i64 to index
    %8 = memref.load %arg0[%7] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<32xi32>
    %9 = arith.extui %4 {handshake.name = "extui1"} : i32 to i64
    %10 = arith.index_cast %9 {handshake.name = "index_cast1"} : i64 to index
    %11 = memref.load %arg1[%10] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<32xi32>
    %12 = arith.muli %8, %11 {handshake.name = "muli0"} : i32
    %13 = arith.addi %5, %12 {handshake.name = "addi2"} : i32
    %14 = arith.addi %4, %c1_i32_1 {handshake.name = "addi3"} : i32
    %15 = arith.cmpi ne, %14, %3 {handshake.name = "cmpi1"} : i32
    cf.cond_br %15, ^bb2(%14, %13 : i32, i32), ^bb3(%13 : i32) {handshake.name = "cond_br1"}
  ^bb3(%16: i32):  // 2 preds: ^bb0, ^bb2
    return {handshake.name = "return0"} %16 : i32
  }
}

