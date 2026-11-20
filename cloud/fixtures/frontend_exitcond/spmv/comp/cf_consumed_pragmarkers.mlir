module {
  func.func @spmv(%arg0: i32 {handshake.arg_name = "n"}, %arg1: memref<11xi32> {handshake.arg_name = "row"}, %arg2: memref<10xi32> {handshake.arg_name = "col"}, %arg3: memref<10xi32> {handshake.arg_name = "val"}, %arg4: memref<10xi32> {handshake.arg_name = "vec"}, %arg5: memref<10xi32> {handshake.arg_name = "out"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = arith.cmpi sgt, %arg0, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c0_i32 : i32), ^bb4(%c0_i32 : i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb3
    %c1_i32 = arith.constant {handshake.name = "constant2"} 1 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant3"} 0 : i32
    %2 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg1[%3] {handshake.name = "load0"} : memref<11xi32>
    %5 = arith.addi %1, %c1_i32 {handshake.name = "addi0"} : i32
    %6 = arith.extui %5 {handshake.name = "extui1"} : i32 to i64
    %7 = arith.index_cast %6 {handshake.name = "index_cast1"} : i64 to index
    %8 = memref.load %arg1[%7] {handshake.name = "load1"} : memref<11xi32>
    %9 = arith.cmpi slt, %4, %8 {handshake.name = "cmpi1"} : i32
    cf.cond_br %9, ^bb2(%4, %c0_i32_0 : i32, i32), ^bb3(%c0_i32_0 : i32) {handshake.name = "cond_br1"}
  ^bb2(%10: i32, %11: i32):  // 2 preds: ^bb1, ^bb2
    %c1_i32_1 = arith.constant {handshake.name = "constant4"} 1 : i32
    %12 = arith.index_cast %10 {handshake.name = "index_cast2"} : i32 to index
    %13 = memref.load %arg3[%12] {handshake.name = "load2"} : memref<10xi32>
    %14 = arith.index_cast %10 {handshake.name = "index_cast3"} : i32 to index
    %15 = memref.load %arg2[%14] {handshake.name = "load3"} : memref<10xi32>
    %16 = arith.index_cast %15 {handshake.name = "index_cast4"} : i32 to index
    %17 = memref.load %arg4[%16] {handshake.name = "load4"} : memref<10xi32>
    %18 = arith.muli %13, %17 {handshake.name = "muli0"} : i32
    %19 = arith.addi %11, %18 {handshake.name = "addi1"} : i32
    %20 = arith.addi %10, %c1_i32_1 {handshake.name = "addi2"} : i32
    %21 = arith.cmpi ne, %20, %8 {handshake.name = "cmpi2"} : i32
    cf.cond_br %21, ^bb2(%20, %19 : i32, i32), ^bb3(%19 : i32) {handshake.name = "cond_br2"}
  ^bb3(%22: i32):  // 2 preds: ^bb1, ^bb2
    %c1_i32_2 = arith.constant {handshake.name = "constant5"} 1 : i32
    %23 = arith.extui %1 {handshake.name = "extui2"} : i32 to i64
    %24 = arith.index_cast %23 {handshake.name = "index_cast5"} : i64 to index
    memref.store %22, %arg5[%24] {handshake.name = "store5"} : memref<10xi32>
    %25 = arith.addi %1, %c1_i32_2 {handshake.name = "addi3"} : i32
    %26 = arith.cmpi ne, %25, %arg0 {handshake.name = "cmpi3"} : i32
    cf.cond_br %26, ^bb1(%25 : i32), ^bb4(%4 : i32) {handshake.name = "cond_br3"}
  ^bb4(%27: i32):  // 2 preds: ^bb0, ^bb3
    return {handshake.name = "return0"} %27 : i32
  }
}

