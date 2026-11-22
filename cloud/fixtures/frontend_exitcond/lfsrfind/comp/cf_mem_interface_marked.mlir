module {
  func.func @lfsrfind(%arg0: i32 {handshake.arg_name = "seed"}, %arg1: i32 {handshake.arg_name = "key"}) -> i32 {
    %c65535_i32 = arith.constant {handshake.name = "constant0"} 65535 : i32
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    %0 = arith.andi %arg0, %c65535_i32 {handshake.name = "andi0"} : i32
    %1 = arith.andi %arg1, %c65535_i32 {handshake.name = "andi1"} : i32
    cf.br ^bb1(%c0_i32, %0 : i32, i32) {handshake.name = "br0"}
  ^bb1(%2: i32, %3: i32):  // 2 preds: ^bb0, ^bb2
    %4 = arith.cmpi eq, %3, %1 {handshake.name = "cmpi0"} : i32
    cf.cond_br %4, ^bb3(%2 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    %c256_i32 = arith.constant {handshake.name = "constant5"} 256 : i32
    %c46080_i32 = arith.constant {handshake.name = "constant6"} 46080 : i32
    %c1_i32 = arith.constant {handshake.name = "constant7"} 1 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant8"} 0 : i32
    %5 = arith.shrui %3, %c1_i32 {handshake.name = "shrui0"} : i32
    %6 = arith.andi %3, %c1_i32 {handshake.name = "andi2"} : i32
    %7 = arith.cmpi eq, %6, %c0_i32_0 {handshake.name = "cmpi1"} : i32
    %8 = arith.select %7, %c0_i32_0, %c46080_i32 {handshake.name = "select0"} : i32
    %9 = arith.xori %5, %8 {handshake.name = "xori0"} : i32
    %10 = arith.addi %2, %c1_i32 {handshake.name = "addi0"} : i32
    %11 = arith.cmpi ne, %10, %c256_i32 {handshake.name = "cmpi2"} : i32
    cf.cond_br %11, ^bb1(%10, %9 : i32, i32), ^bb3(%c256_i32 : i32) {handshake.name = "cond_br1"}
  ^bb3(%12: i32):  // 2 preds: ^bb1, ^bb2
    return {handshake.name = "return0"} %12 : i32
  }
}

