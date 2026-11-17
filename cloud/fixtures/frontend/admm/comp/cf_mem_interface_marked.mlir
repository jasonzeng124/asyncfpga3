module {
  memref.global "private" constant @__const.main.inp : memref<30xf32> = dense<[0.838658094, -0.493658334, -4.557200e-01, -0.182672814, 0.789224267, -0.986266374, -0.112344235, -0.607068598, -0.264422655, 1.00797248, -1.03517795, 0.778603374, -0.219463661, -0.711719334, 0.802783071, 0.763099074, -1.01777542, -0.159266844, -0.49239406, -0.243099123, 0.789343178, -0.217009842, -0.939968109, 0.468218029, 0.20811832, 0.976879715, 0.326607972, 0.014025473, -0.1994313, -4.441970e-01]> {alignment = 16 : i64, handshake.name = "global0"}
  memref.global "private" constant @__const.main.KKT_inv : memref<900xf32> = dense<"0xD72822419FBDC23F24D2A0BE2B2E38BFD7A9003F394B013EE89F3B409FBDC23F24D2203F2B2EB83ED7A9003F394B81BEE89F3B409FBD42C024D2A0BE2B2EB83ED7A980BF394B013E9FBD42C017B3F83F0684C43EA7C4033F54529F3CBC0F033E9FBDC23F17B3F83F068444BFA7C483BE54529F3CBC0F83BE9FBDC23F05CC41410684C43EA7C483BE54521FBDBC0F033EEFF3BFBE1815AF3F9EB2B13F9D60E33EFDDBA6BE3CCA3ABCEFF33F3E1815AF3F4AAD30C09D6063BEFDDBA6BE3CCABA3CEFF33F3E18152FC09EB2B13F9D6063BEFDDB263F3CCA3ABC24D2203F0684C43EB679EB3F013379BF9A8F23BE9BC417BE24D2A0BE0684C43E3D9E44410C34F93E9A8F23BE9BC4973E24D2A0BE068444BFB679EB3F0C34F93E9A8FA33E9BC417BE0DDA013E434076BE3C33B13F38842BC08088073FF76EDDBD0DDA81BD434076BE242E30C05089AC3F8088073FF76E5D3E0DDA81BD4340F63E3C33B13F5089AC3FFB8787BFF76EDDBD2B2E38BFA7C483BE0C34F93E16564941DAB6A63F1CA21D3E2B2EB83EA7C483BE013379BF539AD83FDAB6A63F1BA29DBE2B2EB83EA7C4033F0C34F93E539AD83FC2B125C01CA21D3ED7A980BF54529F3C9A8F23BEC2B125C027B3C83FB092F03ED7A9003F54529F3C9A8FA33EDAB6A63F27B3C83FA59170BFD7A9003F54521FBD9A8F23BEDAB6A63FE14F4D41B092F03E299930BF6A643B3EDAA197BE1DAA9DBF952C923F4ACA113F2999B03E6A643B3EDAA1173FA3AA1D3F952C923F1AC08FBF2999B03E6A64BBBEDAA197BEA3AA1D3F7D2711C04ACA113F394B81BEBC0F033E9BC417BE1BA29DBEB092F03E2C00B43E394B013EBC0F033E9BC4973E1CA21D3EB092F03EA83C7441394B013EBC0F83BE9BC417BE1CA21D3EA59170BF2C00B43E06BC0DBD977ABE3C4DFABEBCFB35F8BCFB548F3D0E68823D06BC8D3C977ABE3C4DFA3E3DFB35783CFB548F3DC224E4BD06BC8D3C977A3EBD4DFABEBCFB35783CFA540FBE0E68823DE89F3B40EFF3BFBE24D2A0BE2B2EB83E299930BF394B013ED7282241EFF33F3E24D2A0BE2B2E38BF2999B03E394B013EE89F3B40EFF33F3E24D2203F2B2EB83E2999B03E394B81BE9FBDC23F18152FC00684C43EA7C483BE6A64BBBEBC0F033E9FBD42C01815AF3F0684C43EA7C4033F6A643B3EBC0F033E9FBDC23F1815AF3F068444BFA7C483BE6A643B3EBC0F83BEEFF33F3EFF7D43419EB2B13F9D6063BED63B933E3CCA3ABCEFF3BFBE9EE5F03F9EB2B13F9D60E33ED63B13BE3CCA3ABCEFF33F3E9EE5F03F4AAD30C09D6063BED63B13BE3CCABA3C24D2A0BE4AAD30C0B679EB3F0C34F93EDAA1173F9BC417BE24D2203F9EB2B13FB679EB3F013379BFDAA197BE9BC417BE24D2A0BE9EB2B13F3D9E44410C34F93EDAA197BE9BC4973E0DDA81BD82B15EBF3C33B13F5089AC3FBE4CEA3CF76EDDBD0DDA013E8DB2DE3E3C33B13F38842BC0B64C6ABCF76EDDBD0DDA81BD8DB2DE3E242E30C05089AC3FB64C6ABCF76E5D3E2B2EB83E9D60E33E0C34F93E539AD83F1DAA9DBF1CA21D3E2B2E38BF9D6063BE0C34F93E16564941A3AA1D3F1CA21D3E2B2EB83E9D6063BE013379BF539AD83FA3AA1D3F1BA29DBED7A9003FFDDB263F9A8F23BEDAB6A63F7D2711C0B092F03ED7A980BFFDDBA6BE9A8F23BEC2B125C0952C923FB092F03ED7A9003FFDDBA6BE9A8FA33EDAB6A63F952C923FA59170BF2999B03ED63B933EDAA197BEA3AA1D3FC6FD5B414ACA113F299930BFD63B13BEDAA197BE1DAA9DBF95FB8D3F4ACA113F2999B03ED63B13BEDAA1173FA3AA1D3F95FB8D3F1AC08FBF394B013E3CCABA3C9BC417BE1CA21D3E1AC08FBF2C00B43E394B81BE3CCA3ABC9BC417BE1BA29DBE4ACA113F2C00B43E394B013E3CCA3ABC9BC4973E1CA21D3E4ACA113FA83C744106BC8D3CBB82ACBB4DFABEBCFB35783CF30742BE0E68823D06BC0DBDBB822C3B4DFABEBCFB35F8BC1F0CC23D0E68823D06BC8D3CBB822C3B4DFA3E3DFB35783C1F0CC23DC224E4BDE89F3B40EFF33F3E0DDA013E2B2EB83E2999B03E06BC0DBDE89F3B40EFF3BFBE0DDA81BD2B2EB83E299930BF06BC8D3CD7282241EFF33F3E0DDA81BD2B2E38BF2999B03E06BC8D3C9FBDC23F1815AF3F4340F63EA7C483BE6A643B3E977A3EBD9FBDC23F18152FC0434076BEA7C483BE6A64BBBE977ABE3C9FBD42C01815AF3F434076BEA7C4033F6A643B3E977ABE3CEFF33F3E9EE5F03F82B15EBF9D6063BED63B13BEBB82ACBBEFF33F3EFF7D43418DB2DE3E9D6063BED63B933EBB822C3BEFF3BFBE9EE5F03F8DB2DE3E9D60E33ED63B13BEBB822C3B24D2A0BE9EB2B13F242E30C00C34F93EDAA197BE4DFA3E3D24D2A0BE4AAD30C03C33B13F0C34F93EDAA1173F4DFABEBC24D2203F9EB2B13F3C33B13F013379BFDAA197BE4DFABEBC0DDA81BD8DB2DE3E0C1F46415089AC3FB64C6ABC302A413D0DDA81BD82B15EBF7D76E53F5089AC3FBE4CEA3C302AC1BC0DDA013E8DB2DE3E7D76E53F38842BC0B64C6ABC302AC1BC2B2EB83E9D6063BE38842BC0539AD83FA3AA1D3FFB35F8BC2B2EB83E9D60E33E5089AC3F539AD83F1DAA9DBFFB35783C2B2E38BF9D6063BE5089AC3F16564941A3AA1D3FFB35783CD7A9003FFDDBA6BEFB8787BFDAB6A63F952C923FFA540FBED7A9003FFDDB263F8088073FDAB6A63F7D2711C0FB548F3DD7A980BFFDDBA6BE8088073FC2B125C0952C923FFB548F3D2999B03ED63B13BEBE4CEA3CA3AA1D3F95FB8D3FF30742BE2999B03ED63B933EB64C6ABCA3AA1D3FC6FD5B411F0CC23D299930BFD63B13BEB64C6ABC1DAA9DBF95FB8D3F1F0CC23D394B013E3CCA3ABCF76E5D3E1CA21D3E4ACA113FC224E4BD394B013E3CCABA3CF76EDDBD1CA21D3E1AC08FBF0E68823D394B81BE3CCA3ABCF76EDDBD1BA29DBE4ACA113F0E68823D06BC8D3CBB822C3B302A413DFB35783C1F0CC23D275C7F4106BC8D3CBB82ACBB302AC1BCFB35783CF30742BE2394433C06BC0DBDBB822C3B302AC1BCFB35F8BC1F0CC23D2394433C9FBD42C0EFF33F3E0DDA81BDD7A980BF2999B03E06BC8D3C9FBDC23FEFF33F3E0DDA013ED7A9003F2999B03E06BC0DBD9FBDC23FEFF3BFBE0DDA81BDD7A9003F299930BF06BC8D3C05CC41411815AF3F434076BE54521FBD6A643B3E977ABE3C17B3F83F1815AF3F4340F63E54529F3C6A643B3E977A3EBD17B3F83F18152FC0434076BE54529F3C6A64BBBE977ABE3C18152FC09EE5F03F8DB2DE3EFDDB263FD63B13BEBB822C3B1815AF3F9EE5F03F82B15EBFFDDBA6BED63B13BEBB82ACBB1815AF3FFF7D43418DB2DE3EFDDBA6BED63B933EBB822C3B068444BF9EB2B13F3C33B13F9A8FA33EDAA197BE4DFABEBC0684C43E9EB2B13F242E30C09A8F23BEDAA197BE4DFA3E3D0684C43E4AAD30C03C33B13F9A8F23BEDAA1173F4DFABEBC4340F63E8DB2DE3E7D76E53FFB8787BFB64C6ABC302AC1BC434076BE8DB2DE3E0C1F46418088073FB64C6ABC302A413D434076BE82B15EBF7D76E53F8088073FBE4CEA3C302AC1BCA7C4033F9D6063BE5089AC3FC2B125C0A3AA1D3FFB35783CA7C483BE9D6063BE38842BC0DAB6A63FA3AA1D3FFB35F8BCA7C483BE9D60E33E5089AC3FDAB6A63F1DAA9DBFFB35783C54521FBDFDDBA6BE8088073FE14F4D41952C923FFB548F3D54529F3CFDDBA6BEFB8787BF27B3C83F952C923FFA540FBE54529F3CFDDB263F8088073F27B3C83F7D2711C0FB548F3D6A64BBBED63B13BEB64C6ABC7D2711C095FB8D3F1F0CC23D6A643B3ED63B13BEBE4CEA3C952C923F95FB8D3FF30742BE6A643B3ED63B933EB64C6ABC952C923FC6FD5B411F0CC23DBC0F83BE3CCA3ABCF76EDDBDA59170BF4ACA113F0E68823DBC0F033E3CCA3ABCF76E5D3EB092F03E4ACA113FC224E4BDBC0F033E3CCABA3CF76EDDBDB092F03E1AC08FBF0E68823D977A3EBDBB822C3B302AC1BCFA540FBE1F0CC23D2394433C977ABE3CBB822C3B302A413DFB548F3D1F0CC23D275C7F41977ABE3CBB82ACBB302AC1BCFB548F3DF30742BE2394433C9FBDC23F24D2203F0DDA81BDD7A9003F394B81BE06BC8D3C9FBD42C024D2A0BE0DDA81BDD7A980BF394B013E06BC8D3C9FBDC23F24D2A0BE0DDA013ED7A9003F394B013E06BC0DBD17B3F83F068444BF434076BE54529F3CBC0F83BE977ABE3C05CC41410684C43E434076BE54521FBDBC0F033E977ABE3C17B3F83F0684C43E4340F63E54529F3CBC0F033E977A3EBD1815AF3F4AAD30C08DB2DE3EFDDBA6BE3CCABA3CBB822C3B18152FC09EB2B13F8DB2DE3EFDDB263F3CCA3ABCBB822C3B1815AF3F9EB2B13F82B15EBFFDDBA6BE3CCA3ABCBB82ACBB0684C43E3D9E44413C33B13F9A8F23BE9BC4973E4DFABEBC068444BFB679EB3F3C33B13F9A8FA33E9BC417BE4DFABEBC0684C43EB679EB3F242E30C09A8F23BE9BC417BE4DFA3E3D434076BE242E30C07D76E53F8088073FF76E5D3E302AC1BC4340F63E3C33B13F7D76E53FFB8787BFF76EDDBD302AC1BC434076BE3C33B13F0C1F46418088073FF76EDDBD302A413DA7C483BE013379BF5089AC3FDAB6A63F1BA29DBEFB35783CA7C4033F0C34F93E5089AC3FC2B125C01CA21D3EFB35783CA7C483BE0C34F93E38842BC0DAB6A63F1CA21D3EFB35F8BC54529F3C9A8FA33E8088073F27B3C83FA59170BFFB548F3D54521FBD9A8F23BE8088073FE14F4D41B092F03EFB548F3D54529F3C9A8F23BEFB8787BF27B3C83FB092F03EFA540FBE6A643B3EDAA1173FB64C6ABC952C923F1AC08FBF1F0CC23D6A64BBBEDAA197BEB64C6ABC7D2711C04ACA113F1F0CC23D6A643B3EDAA197BEBE4CEA3C952C923F4ACA113FF30742BEBC0F033E9BC4973EF76EDDBDB092F03EA83C74410E68823DBC0F83BE9BC417BEF76EDDBDA59170BF2C00B43E0E68823DBC0F033E9BC417BEF76E5D3EB092F03E2C00B43EC224E4BD977ABE3C4DFA3E3D302AC1BCFB548F3DC224E4BD2394433C977A3EBD4DFABEBC302AC1BCFA540FBE0E68823D2394433C977ABE3C4DFABEBC302A413DFB548F3D0E68823D275C7F41"> {alignment = 16 : i64, handshake.name = "global1"}
  func.func @admm(%arg0: f32 {handshake.arg_name = "vdc"}, %arg1: memref<30xf32> {handshake.arg_name = "inp"}, %arg2: memref<900xf32> {handshake.arg_name = "KKT_inv"}, %arg3: memref<2xf32> {handshake.arg_name = "out"}, %arg4: memref<30xf32> {handshake.arg_name = "x"}, %arg5: memref<30xf32> {handshake.arg_name = "z"}, %arg6: memref<30xf32> {handshake.arg_name = "y"}, %arg7: memref<30xf32> {handshake.arg_name = "rhs"}, %arg8: memref<30xf32> {handshake.arg_name = "temp_x_tilde"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %c30_i32 = arith.constant {handshake.name = "constant16"} 30 : i32
    %c1_i32 = arith.constant {handshake.name = "constant17"} 1 : i32
    %cst = arith.constant {handshake.name = "constant18"} 0.000000e+00 : f32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg1[%2] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<30xf32>
    %4 = arith.negf %3 {handshake.name = "negf0"} : f32
    %5 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %6 = arith.index_cast %5 {handshake.name = "index_cast1"} : i64 to index
    memref.store %4, %arg7[%6] {handshake.deps = #handshake<deps[{dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load23", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load25", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store22", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store1"} : memref<30xf32>
    %7 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %8 = arith.index_cast %7 {handshake.name = "index_cast2"} : i64 to index
    memref.store %cst, %arg4[%8] {handshake.deps = #handshake<deps[{dstAccess : "load11", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load19", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store12", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store2"} : memref<30xf32>
    %9 = arith.extui %0 {handshake.name = "extui3"} : i32 to i64
    %10 = arith.index_cast %9 {handshake.name = "index_cast3"} : i64 to index
    memref.store %cst, %arg5[%10] {handshake.deps = #handshake<deps[{dstAccess : "load14", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load20", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store16", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store3"} : memref<30xf32>
    %11 = arith.extui %0 {handshake.name = "extui4"} : i32 to i64
    %12 = arith.index_cast %11 {handshake.name = "index_cast4"} : i64 to index
    memref.store %cst, %arg6[%12] {handshake.deps = #handshake<deps[{dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load17", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load21", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store18", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store4"} : memref<30xf32>
    %13 = arith.addi %0, %c1_i32 {handshake.name = "addi0"} : i32
    %14 = arith.cmpi ult, %13, %c30_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %14, ^bb1(%13 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    %cst_0 = arith.constant {handshake.name = "constant19"} 5.000000e-01 : f32
    %c0_i32_1 = arith.constant {handshake.name = "constant20"} 0 : i32
    %15 = arith.mulf %arg0, %cst_0 {handshake.name = "mulf0"} : f32
    %16 = arith.negf %15 {handshake.name = "negf1"} : f32
    cf.br ^bb3(%c0_i32_1 : i32) {handshake.name = "br1"}
  ^bb3(%17: i32):  // 2 preds: ^bb2, ^bb9
    %c0_i32_2 = arith.constant {handshake.name = "constant21"} 0 : i32
    cf.br ^bb4(%c0_i32_2 : i32) {handshake.name = "br2"}
  ^bb4(%18: i32):  // 2 preds: ^bb3, ^bb4
    %c30_i32_3 = arith.constant {handshake.name = "constant22"} 30 : i32
    %c1_i32_4 = arith.constant {handshake.name = "constant23"} 1 : i32
    %cst_5 = arith.constant {handshake.name = "constant24"} 0.000000e+00 : f32
    %c0_i32_6 = arith.constant {handshake.name = "constant25"} 0 : i32
    %19 = arith.extui %18 {handshake.name = "extui5"} : i32 to i64
    %20 = arith.index_cast %19 {handshake.name = "index_cast5"} : i64 to index
    memref.store %cst_5, %arg8[%20] {handshake.deps = #handshake<deps[{dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load13", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store9", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store5"} : memref<30xf32>
    %21 = arith.addi %18, %c1_i32_4 {handshake.name = "addi1"} : i32
    %22 = arith.cmpi ult, %21, %c30_i32_3 {handshake.name = "cmpi1"} : i32
    cf.cond_br %22, ^bb4(%21 : i32), ^bb5(%c0_i32_6 : i32) {handshake.name = "cond_br1"}
  ^bb5(%23: i32):  // 2 preds: ^bb4, ^bb7
    %c0_i32_7 = arith.constant {handshake.name = "constant26"} 0 : i32
    %24 = arith.extui %23 {handshake.name = "extui6"} : i32 to i64
    %25 = arith.extui %23 {handshake.name = "extui7"} : i32 to i64
    %26 = arith.index_cast %25 {handshake.name = "index_cast6"} : i64 to index
    %27 = memref.load %arg8[%26] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load6"} : memref<30xf32>
    cf.br ^bb6(%c0_i32_7, %27 : i32, f32) {handshake.name = "br3"}
  ^bb6(%28: i32, %29: f32):  // 2 preds: ^bb5, ^bb6
    %c30_i32_8 = arith.constant {handshake.name = "constant27"} 30 : i32
    %c1_i32_9 = arith.constant {handshake.name = "constant28"} 1 : i32
    %c4_i64 = arith.constant {handshake.name = "constant29"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant30"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant31"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant32"} 1 : i64
    %30 = arith.extui %28 {handshake.name = "extui8"} : i32 to i64
    %31 = arith.shli %24, %c1_i64 {handshake.name = "shli0"} : i64
    %32 = arith.shli %24, %c2_i64 {handshake.name = "shli1"} : i64
    %33 = arith.addi %31, %32 {handshake.name = "addi7"} : i64
    %34 = arith.shli %24, %c3_i64 {handshake.name = "shli2"} : i64
    %35 = arith.shli %24, %c4_i64 {handshake.name = "shli3"} : i64
    %36 = arith.addi %34, %35 {handshake.name = "addi8"} : i64
    %37 = arith.addi %33, %36 {handshake.name = "addi9"} : i64
    %38 = arith.addi %37, %30 {handshake.name = "addi2"} : i64
    %39 = arith.index_cast %38 {handshake.name = "index_cast7"} : i64 to index
    %40 = memref.load %arg2[%39] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load7"} : memref<900xf32>
    %41 = arith.extui %28 {handshake.name = "extui9"} : i32 to i64
    %42 = arith.index_cast %41 {handshake.name = "index_cast8"} : i64 to index
    %43 = memref.load %arg7[%42] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load8"} : memref<30xf32>
    %44 = arith.mulf %40, %43 {handshake.name = "mulf1"} : f32
    %45 = arith.addf %29, %44 {handshake.name = "addf0"} : f32
    %46 = arith.index_cast %25 {handshake.name = "index_cast9"} : i64 to index
    memref.store %45, %arg8[%46] {handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load13", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 3>, handshake.name = "store9"} : memref<30xf32>
    %47 = arith.addi %28, %c1_i32_9 {handshake.name = "addi3"} : i32
    %48 = arith.cmpi ult, %47, %c30_i32_8 {handshake.name = "cmpi2"} : i32
    cf.cond_br %48, ^bb6(%47, %45 : i32, f32), ^bb7 {handshake.name = "cond_br2"}
  ^bb7:  // pred: ^bb6
    %cst_10 = arith.constant {handshake.name = "constant33"} 1.000000e-01 : f32
    %cst_11 = arith.constant {handshake.name = "constant34"} 1.000000e+01 : f32
    %cst_12 = arith.constant {handshake.name = "constant35"} -6.000000e-01 : f32
    %c30_i32_13 = arith.constant {handshake.name = "constant36"} 30 : i32
    %c1_i32_14 = arith.constant {handshake.name = "constant37"} 1 : i32
    %c0_i32_15 = arith.constant {handshake.name = "constant38"} 0 : i32
    %49 = arith.extui %23 {handshake.name = "extui10"} : i32 to i64
    %50 = arith.index_cast %49 {handshake.name = "index_cast10"} : i64 to index
    %51 = memref.load %arg8[%50] {handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load10"} : memref<30xf32>
    %52 = arith.extui %23 {handshake.name = "extui11"} : i32 to i64
    %53 = arith.index_cast %52 {handshake.name = "index_cast11"} : i64 to index
    %54 = memref.load %arg4[%53] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load11"} : memref<30xf32>
    %55 = arith.mulf %54, %cst_12 {handshake.name = "mulf2"} : f32
    %56 = arith.addf %51, %55 {handshake.name = "addf1"} : f32
    %57 = arith.extui %23 {handshake.name = "extui12"} : i32 to i64
    %58 = arith.index_cast %57 {handshake.name = "index_cast12"} : i64 to index
    memref.store %56, %arg4[%58] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load11", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load19", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store12"} : memref<30xf32>
    %59 = arith.extui %23 {handshake.name = "extui13"} : i32 to i64
    %60 = arith.index_cast %59 {handshake.name = "index_cast13"} : i64 to index
    %61 = memref.load %arg8[%60] {handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load13"} : memref<30xf32>
    %62 = arith.extui %23 {handshake.name = "extui14"} : i32 to i64
    %63 = arith.index_cast %62 {handshake.name = "index_cast14"} : i64 to index
    %64 = memref.load %arg5[%63] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load14"} : memref<30xf32>
    %65 = arith.mulf %64, %cst_12 {handshake.name = "mulf3"} : f32
    %66 = arith.addf %61, %65 {handshake.name = "addf2"} : f32
    %67 = arith.extui %23 {handshake.name = "extui15"} : i32 to i64
    %68 = arith.index_cast %67 {handshake.name = "index_cast15"} : i64 to index
    %69 = memref.load %arg6[%68] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load15"} : memref<30xf32>
    %70 = arith.mulf %69, %cst_11 {handshake.name = "mulf4"} : f32
    %71 = arith.addf %66, %70 {handshake.name = "addf3"} : f32
    %72 = arith.cmpf olt, %71, %16 {handshake.name = "cmpf0"} : f32
    %73 = arith.cmpf ogt, %71, %15 {handshake.name = "cmpf1"} : f32
    %74 = arith.select %73, %15, %71 {handshake.name = "select0"} : f32
    %75 = arith.select %72, %16, %74 {handshake.name = "select1"} : f32
    %76 = arith.extui %23 {handshake.name = "extui16"} : i32 to i64
    %77 = arith.index_cast %76 {handshake.name = "index_cast16"} : i64 to index
    memref.store %75, %arg5[%77] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load14", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load20", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store16"} : memref<30xf32>
    %78 = arith.extui %23 {handshake.name = "extui17"} : i32 to i64
    %79 = arith.index_cast %78 {handshake.name = "index_cast17"} : i64 to index
    %80 = memref.load %arg6[%79] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load17"} : memref<30xf32>
    %81 = arith.subf %66, %75 {handshake.name = "subf0"} : f32
    %82 = arith.mulf %81, %cst_10 {handshake.name = "mulf5"} : f32
    %83 = arith.addf %80, %82 {handshake.name = "addf4"} : f32
    %84 = arith.extui %23 {handshake.name = "extui18"} : i32 to i64
    %85 = arith.index_cast %84 {handshake.name = "index_cast18"} : i64 to index
    memref.store %83, %arg6[%85] {handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load17", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load21", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store18"} : memref<30xf32>
    %86 = arith.addi %23, %c1_i32_14 {handshake.name = "addi4"} : i32
    %87 = arith.cmpi ult, %86, %c30_i32_13 {handshake.name = "cmpi3"} : i32
    cf.cond_br %87, ^bb5(%86 : i32), ^bb8(%c0_i32_15 : i32) {handshake.name = "cond_br3"}
  ^bb8(%88: i32):  // 2 preds: ^bb7, ^bb8
    %cst_16 = arith.constant {handshake.name = "constant39"} 1.000000e-01 : f32
    %c30_i32_17 = arith.constant {handshake.name = "constant40"} 30 : i32
    %c1_i32_18 = arith.constant {handshake.name = "constant41"} 1 : i32
    %89 = arith.extui %88 {handshake.name = "extui19"} : i32 to i64
    %90 = arith.index_cast %89 {handshake.name = "index_cast19"} : i64 to index
    %91 = memref.load %arg4[%90] {handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load19"} : memref<30xf32>
    %92 = arith.extui %88 {handshake.name = "extui20"} : i32 to i64
    %93 = arith.index_cast %92 {handshake.name = "index_cast20"} : i64 to index
    %94 = memref.load %arg5[%93] {handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load20"} : memref<30xf32>
    %95 = arith.mulf %94, %cst_16 {handshake.name = "mulf6"} : f32
    %96 = arith.addf %91, %95 {handshake.name = "addf5"} : f32
    %97 = arith.extui %88 {handshake.name = "extui21"} : i32 to i64
    %98 = arith.index_cast %97 {handshake.name = "index_cast21"} : i64 to index
    %99 = memref.load %arg6[%98] {handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load21"} : memref<30xf32>
    %100 = arith.subf %96, %99 {handshake.name = "subf1"} : f32
    %101 = arith.extui %88 {handshake.name = "extui22"} : i32 to i64
    %102 = arith.index_cast %101 {handshake.name = "index_cast22"} : i64 to index
    memref.store %100, %arg7[%102] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load23", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load25", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 3>, handshake.name = "store22"} : memref<30xf32>
    %103 = arith.addi %88, %c1_i32_18 {handshake.name = "addi5"} : i32
    %104 = arith.cmpi ult, %103, %c30_i32_17 {handshake.name = "cmpi4"} : i32
    cf.cond_br %104, ^bb8(%103 : i32), ^bb9 {handshake.name = "cond_br4"}
  ^bb9:  // pred: ^bb8
    %c7_i32 = arith.constant {handshake.name = "constant42"} 7 : i32
    %c1_i32_19 = arith.constant {handshake.name = "constant43"} 1 : i32
    %105 = arith.addi %17, %c1_i32_19 {handshake.name = "addi6"} : i32
    %106 = arith.cmpi ult, %105, %c7_i32 {handshake.name = "cmpi5"} : i32
    cf.cond_br %106, ^bb3(%105 : i32), ^bb10 {handshake.name = "cond_br5"}
  ^bb10:  // pred: ^bb9
    %c0 = arith.constant {handshake.name = "constant44"} 0 : index
    %c1 = arith.constant {handshake.name = "constant45"} 1 : index
    %107 = memref.load %arg7[%c0] {handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load23"} : memref<30xf32>
    memref.store %107, %arg3[%c0] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store24"} : memref<2xf32>
    %108 = memref.load %arg7[%c1] {handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load25"} : memref<30xf32>
    memref.store %108, %arg3[%c1] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store26"} : memref<2xf32>
    return {handshake.name = "return0"}
  }
}

