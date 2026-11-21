module {
  func.func @if_loop_2(%arg0: memref<100xi32> {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "n"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = arith.cmpi sgt, %arg1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c0_i32 : i32, i32), ^bb2(%c0_i32 : i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant3"} 1 : i32
    %c10_i32 = arith.constant {handshake.name = "constant4"} 10 : i32
    %3 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %4 = arith.index_cast %3 {handshake.name = "index_cast0"} : i64 to index
    %5 = memref.load %arg0[%4] {handshake.name = "load0"} : memref<100xi32>
    %6 = arith.cmpi sgt, %5, %c10_i32 {handshake.name = "cmpi1"} : i32
    %7 = arith.addi %2, %5 {handshake.name = "addi0"} : i32
    %8 = arith.select %6, %7, %2 {handshake.name = "select0"} : i32
    %9 = arith.addi %1, %c1_i32 {handshake.name = "addi1"} : i32
    %10 = arith.cmpi ne, %9, %arg1 {handshake.name = "cmpi2"} : i32
    cf.cond_br %10, ^bb1(%9, %8 : i32, i32), ^bb2(%8 : i32) {handshake.name = "cond_br1"}
  ^bb2(%11: i32):  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"} %11 : i32
  }
}

