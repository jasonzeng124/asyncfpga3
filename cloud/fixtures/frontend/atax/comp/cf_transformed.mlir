module {
  func.func @atax(%arg0: memref<400xi32> {handshake.arg_name = "A"}, %arg1: memref<20xi32> {handshake.arg_name = "x"}, %arg2: memref<20xi32> {handshake.arg_name = "y"}, %arg3: memref<20xi32> {handshake.arg_name = "tmp"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %c0_i32_0 = arith.constant {handshake.name = "constant6"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg3[%2] {handshake.name = "load0"} : memref<20xi32>
    %4 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    cf.br ^bb2(%3, %c0_i32_0 : i32, i32) {handshake.name = "br1"}
  ^bb2(%5: i32, %6: i32):  // 2 preds: ^bb1, ^bb2
    %c20_i32 = arith.constant {handshake.name = "constant7"} 20 : i32
    %c1_i32 = arith.constant {handshake.name = "constant8"} 1 : i32
    %c4_i64 = arith.constant {handshake.name = "constant9"} 4 : i64
    %c2_i64 = arith.constant {handshake.name = "constant10"} 2 : i64
    %7 = arith.extui %6 {handshake.name = "extui2"} : i32 to i64
    %8 = arith.shli %4, %c2_i64 {handshake.name = "shli0"} : i64
    %9 = arith.shli %4, %c4_i64 {handshake.name = "shli1"} : i64
    %10 = arith.addi %8, %9 {handshake.name = "addi7"} : i64
    %11 = arith.addi %10, %7 {handshake.name = "addi0"} : i64
    %12 = arith.index_cast %11 {handshake.name = "index_cast1"} : i64 to index
    %13 = memref.load %arg0[%12] {handshake.name = "load1"} : memref<400xi32>
    %14 = arith.extui %6 {handshake.name = "extui3"} : i32 to i64
    %15 = arith.index_cast %14 {handshake.name = "index_cast2"} : i64 to index
    %16 = memref.load %arg1[%15] {handshake.name = "load2"} : memref<20xi32>
    %17 = arith.muli %13, %16 {handshake.name = "muli1"} : i32
    %18 = arith.addi %5, %17 {handshake.name = "addi1"} : i32
    %19 = arith.addi %6, %c1_i32 {handshake.name = "addi2"} : i32
    %20 = arith.cmpi ult, %19, %c20_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %20, ^bb2(%18, %19 : i32, i32), ^bb3(%18 : i32) {handshake.name = "cond_br0"}
  ^bb3(%21: i32):  // pred: ^bb2
    %c0_i32_1 = arith.constant {handshake.name = "constant11"} 0 : i32
    %22 = arith.extui %0 {handshake.name = "extui4"} : i32 to i64
    cf.br ^bb4(%c0_i32_1 : i32) {handshake.name = "br2"}
  ^bb4(%23: i32):  // 2 preds: ^bb3, ^bb4
    %c20_i32_2 = arith.constant {handshake.name = "constant12"} 20 : i32
    %c1_i32_3 = arith.constant {handshake.name = "constant13"} 1 : i32
    %c4_i64_4 = arith.constant {handshake.name = "constant14"} 4 : i64
    %c2_i64_5 = arith.constant {handshake.name = "constant15"} 2 : i64
    %24 = arith.extui %23 {handshake.name = "extui5"} : i32 to i64
    %25 = arith.index_cast %24 {handshake.name = "index_cast3"} : i64 to index
    %26 = memref.load %arg2[%25] {handshake.name = "load3"} : memref<20xi32>
    %27 = arith.extui %23 {handshake.name = "extui6"} : i32 to i64
    %28 = arith.shli %22, %c2_i64_5 {handshake.name = "shli2"} : i64
    %29 = arith.shli %22, %c4_i64_4 {handshake.name = "shli3"} : i64
    %30 = arith.addi %28, %29 {handshake.name = "addi8"} : i64
    %31 = arith.addi %30, %27 {handshake.name = "addi3"} : i64
    %32 = arith.index_cast %31 {handshake.name = "index_cast4"} : i64 to index
    %33 = memref.load %arg0[%32] {handshake.name = "load4"} : memref<400xi32>
    %34 = arith.muli %33, %21 {handshake.name = "muli3"} : i32
    %35 = arith.addi %26, %34 {handshake.name = "addi4"} : i32
    %36 = arith.extui %23 {handshake.name = "extui7"} : i32 to i64
    %37 = arith.index_cast %36 {handshake.name = "index_cast5"} : i64 to index
    memref.store %35, %arg2[%37] {handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<20xi32>
    %38 = arith.addi %23, %c1_i32_3 {handshake.name = "addi5"} : i32
    %39 = arith.cmpi ult, %38, %c20_i32_2 {handshake.name = "cmpi1"} : i32
    cf.cond_br %39, ^bb4(%38 : i32), ^bb5 {handshake.name = "cond_br1"}
  ^bb5:  // pred: ^bb4
    %c20_i32_6 = arith.constant {handshake.name = "constant16"} 20 : i32
    %c1_i32_7 = arith.constant {handshake.name = "constant17"} 1 : i32
    %40 = arith.extui %0 {handshake.name = "extui8"} : i32 to i64
    %41 = arith.index_cast %40 {handshake.name = "index_cast6"} : i64 to index
    memref.store %21, %arg3[%41] {handshake.name = "store6"} : memref<20xi32>
    %42 = arith.addi %0, %c1_i32_7 {handshake.name = "addi6"} : i32
    %43 = arith.cmpi ult, %42, %c20_i32_6 {handshake.name = "cmpi2"} : i32
    cf.cond_br %43, ^bb1(%42 : i32), ^bb6 {handshake.name = "cond_br2"}
  ^bb6:  // pred: ^bb5
    return {handshake.name = "return0"}
  }
}

