module {
  memref.global "private" constant @".str" : memref<9xi8> = dense<[115, 116, 97, 110, 100, 97, 114, 100, 0]> {alignment = 1 : i64, handshake.name = "global0"}
  func.func @single_loop(%arg0: memref<1000xi32> {handshake.arg_name = "a"}, %arg1: memref<1000xi32> {handshake.arg_name = "b"}, %arg2: memref<1000xi32> {handshake.arg_name = "c"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant2"} 1 : i32
    %c1000_i32 = arith.constant {handshake.name = "constant4"} 1000 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg0[%2] {handshake.name = "load0"} : memref<1000xi32>
    %4 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %5 = arith.index_cast %4 {handshake.name = "index_cast1"} : i64 to index
    %6 = memref.load %arg1[%5] {handshake.name = "load1"} : memref<1000xi32>
    %7 = arith.muli %3, %6 {handshake.name = "muli0"} : i32
    %8 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %9 = arith.index_cast %8 {handshake.name = "index_cast2"} : i64 to index
    memref.store %7, %arg2[%9] {handshake.name = "store2"} : memref<1000xi32>
    %10 = arith.cmpi slt, %7, %c1000_i32 {handshake.name = "cmpi0"} : i32
    %11 = "dynamatic.producer_output_attr_marker"(%10) {dynamatic.speculate = {max_predictions = 7 : i64, style = "standard"}, handshake.name = "producer_output_attr_marker0"} : (i1) -> i1
    %12 = arith.addi %0, %c1_i32 {handshake.name = "addi0"} : i32
    cf.cond_br %11, ^bb1(%12 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    return {handshake.name = "return0"}
  }
}

