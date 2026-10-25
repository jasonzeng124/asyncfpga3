module {
  func.func @ipow(%arg0: i32 {handshake.arg_name = "b"}, %arg1: i32 {handshake.arg_name = "e"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %c1_i32 = arith.constant {handshake.name = "constant1"} 1 : i32
    %0 = arith.cmpi sgt, %arg1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%arg0, %arg1, %c1_i32 : i32, i32, i32), ^bb2(%c1_i32 : i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32, %3: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32_0 = arith.constant {handshake.name = "constant2"} 1 : i32
    %c0_i32_1 = arith.constant {handshake.name = "constant3"} 0 : i32
    %4 = arith.andi %2, %c1_i32_0 {handshake.name = "andi0"} : i32
    %5 = arith.cmpi eq, %4, %c0_i32_1 {handshake.name = "cmpi1"} : i32
    %6 = arith.muli %3, %1 {handshake.name = "muli0"} : i32
    %7 = arith.select %5, %3, %6 {handshake.name = "select0"} : i32
    %8 = arith.muli %1, %1 {handshake.name = "muli1"} : i32
    %9 = arith.shrsi %2, %c1_i32_0 {handshake.name = "shrsi0"} : i32
    %10 = arith.cmpi sgt, %9, %c0_i32_1 {handshake.name = "cmpi2"} : i32
    cf.cond_br %10, ^bb1(%8, %9, %7 : i32, i32, i32), ^bb2(%7 : i32) {handshake.name = "cond_br1"}
  ^bb2(%11: i32):  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"} %11 : i32
  }
}

