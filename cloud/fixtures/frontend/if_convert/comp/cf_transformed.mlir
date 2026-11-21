module {
  memref.global "private" constant @".str" : memref<9xi8> = dense<[115, 116, 97, 110, 100, 97, 114, 100, 0]> {alignment = 1 : i64, handshake.name = "global0"}
  func.func @if_convert(%arg0: memref<200xi32> {handshake.arg_name = "a"}, %arg1: memref<200xi32> {handshake.arg_name = "b"}) {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    cf.br ^bb1(%c1_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %c198_i32 = arith.constant {handshake.name = "constant2"} 198 : i32
    %c10000_i32 = arith.constant {handshake.name = "constant4"} 10000 : i32
    %c1_i32_0 = arith.constant {handshake.name = "constant5"} 1 : i32
    %1 = arith.index_cast %0 {handshake.name = "index_cast0"} : i32 to index
    %2 = memref.load %arg0[%1] {handshake.name = "load0"} : memref<200xi32>
    %3 = arith.muli %0, %2 {handshake.name = "muli0"} : i32
    %4 = arith.cmpi slt, %3, %c10000_i32 {handshake.name = "cmpi0"} : i32
    %5 = "dynamatic.producer_output_attr_marker"(%4) {dynamatic.speculate = {max_predictions = 8 : i64, style = "standard"}, handshake.name = "producer_output_attr_marker0"} : (i1) -> i1
    %6 = arith.addi %0, %c1_i32_0 {handshake.name = "addi0"} : i32
    %7 = arith.select %5, %6, %0 {handshake.name = "select0"} : i32
    %8 = arith.addi %7, %c1_i32_0 {handshake.name = "addi1"} : i32
    %9 = arith.index_cast %8 {handshake.name = "index_cast1"} : i32 to index
    memref.store %c1_i32_0, %arg1[%9] {handshake.name = "store1"} : memref<200xi32>
    %10 = arith.cmpi slt, %7, %c198_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %10, ^bb1(%8 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    return {handshake.name = "return0"}
  }
}

