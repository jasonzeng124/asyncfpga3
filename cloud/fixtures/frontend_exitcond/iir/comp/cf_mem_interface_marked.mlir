module {
  func.func @iir(%arg0: memref<1000xi32> {handshake.arg_name = "y"}, %arg1: memref<1000xi32> {handshake.arg_name = "x"}, %arg2: i32 {handshake.arg_name = "a"}, %arg3: i32 {handshake.arg_name = "b"}) -> i32 {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    %c0 = arith.constant {handshake.name = "constant2"} 0 : index
    %0 = memref.load %arg0[%c0] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<1000xi32>
    cf.br ^bb1(%c1_i32, %0 : i32, i32) {handshake.name = "br0"}
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %c1000_i32 = arith.constant {handshake.name = "constant3"} 1000 : i32
    %c1_i32_0 = arith.constant {handshake.name = "constant4"} 1 : i32
    %3 = arith.muli %2, %arg2 {handshake.name = "muli0"} : i32
    %4 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %5 = arith.index_cast %4 {handshake.name = "index_cast0"} : i64 to index
    %6 = memref.load %arg1[%5] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<1000xi32>
    %7 = arith.muli %6, %arg3 {handshake.name = "muli1"} : i32
    %8 = arith.addi %3, %7 {handshake.name = "addi0"} : i32
    %9 = arith.extui %1 {handshake.name = "extui1"} : i32 to i64
    %10 = arith.index_cast %9 {handshake.name = "index_cast1"} : i64 to index
    memref.store %8, %arg0[%10] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : memref<1000xi32>
    %11 = arith.addi %1, %c1_i32_0 {handshake.name = "addi1"} : i32
    %12 = arith.cmpi ne, %11, %c1000_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %12, ^bb1(%11, %8 : i32, i32), ^bb2(%8 : i32) {handshake.name = "cond_br0"}
  ^bb2(%13: i32):  // pred: ^bb1
    return {handshake.name = "return0"} %13 : i32
  }
}

