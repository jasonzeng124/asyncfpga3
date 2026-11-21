module {
  func.func @iterative_sqrt(%arg0: i32 {handshake.arg_name = "n"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = arith.cmpi slt, %arg0, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb3(%arg0 : i32), ^bb1(%arg0, %c0_i32 : i32, i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb2
    %c1_i32 = arith.constant {handshake.name = "constant3"} 1 : i32
    %3 = arith.addi %2, %1 {handshake.name = "addi0"} : i32
    %4 = arith.shrsi %3, %c1_i32 {handshake.name = "shrsi0"} : i32
    %5 = arith.muli %4, %4 {handshake.name = "muli0"} : i32
    %6 = arith.cmpi eq, %5, %arg0 {handshake.name = "cmpi1"} : i32
    cf.cond_br %6, ^bb3(%4 : i32), ^bb2 {handshake.name = "cond_br1"}
  ^bb2:  // pred: ^bb1
    %c-1_i32 = arith.constant {handshake.name = "constant4"} -1 : i32
    %c1_i32_0 = arith.constant {handshake.name = "constant5"} 1 : i32
    %7 = arith.muli %4, %4 {handshake.name = "muli1"} : i32
    %8 = arith.cmpi slt, %7, %arg0 {handshake.name = "cmpi2"} : i32
    %9 = arith.addi %4, %c1_i32_0 {handshake.name = "addi1"} : i32
    %10 = arith.addi %4, %c-1_i32 {handshake.name = "addi2"} : i32
    %11 = arith.select %8, %9, %2 {handshake.name = "select0"} : i32
    %12 = arith.select %8, %1, %10 {handshake.name = "select1"} : i32
    %13 = arith.cmpi sgt, %11, %12 {handshake.name = "cmpi3"} : i32
    cf.cond_br %13, ^bb3(%12 : i32), ^bb1(%12, %11 : i32, i32) {handshake.name = "cond_br2"}
  ^bb3(%14: i32):  // 3 preds: ^bb0, ^bb1, ^bb2
    return {handshake.name = "return0"} %14 : i32
  }
}

