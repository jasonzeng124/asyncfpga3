module {
  func.func @sumi3_mem(%arg0: memref<1000xi32> {handshake.arg_name = "a"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32) {handshake.name = "br0"}
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb1
    %c1000_i32 = arith.constant {handshake.name = "constant3"} 1000 : i32
    %c1_i32 = arith.constant {handshake.name = "constant4"} 1 : i32
    %2 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<1000xi32>
    %5 = arith.muli %4, %4 {handshake.name = "muli0"} : i32
    %6 = arith.muli %5, %4 {handshake.name = "muli1"} : i32
    %7 = arith.addi %1, %6 {handshake.name = "addi0"} : i32
    %8 = arith.addi %0, %c1_i32 {handshake.name = "addi1"} : i32
    %9 = arith.cmpi ult, %8, %c1000_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %9, ^bb1(%8, %7 : i32, i32), ^bb2(%7 : i32) {handshake.name = "cond_br0"}
  ^bb2(%10: i32):  // pred: ^bb1
    return {handshake.name = "return0"} %10 : i32
  }
}

