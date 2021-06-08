(* spreads and packings of pg32 *)

Require Import ssreflect ssrfun ssrbool.
Require Import Generic.lemmas Generic.wlog.
Require Import PG32.pg32_inductive.
Require Import Lists.List.

Import ListNotations.

Definition S0 := [ L0; L19; L24; L28; L33 ].
Definition S1 := [ L0; L19; L26; L29; L32 ].
Definition S2 := [ L0; L20; L23; L28; L34 ].
Definition S3 := [ L0; L20; L25; L29; L31 ].
Definition S4 := [ L0; L21; L24; L30; L31 ].
Definition S5 := [ L0; L21; L26; L27; L34 ].
Definition S6 := [ L0; L22; L23; L30; L32 ].
Definition S7 := [ L0; L22; L25; L27; L33 ].
Definition S8 := [ L1; L8; L14; L28; L33 ].
Definition S9 := [ L1; L8; L16; L29; L31 ].
Definition S10 := [ L1; L9; L13; L29; L32 ].
Definition S11 := [ L1; L9; L18; L28; L34 ].
Definition S12 := [ L1; L10; L14; L30; L32 ].
Definition S13 := [ L1; L10; L16; L27; L34 ].
Definition S14 := [ L1; L11; L13; L27; L33 ].
Definition S15 := [ L1; L11; L18; L30; L31 ].
Definition S16 := [ L2; L8; L14; L21; L26 ].
Definition S17 := [ L2; L8; L16; L22; L23 ].
Definition S18 := [ L2; L9; L13; L21; L24 ].
Definition S19 := [ L2; L9; L18; L22; L25 ].
Definition S20 := [ L2; L10; L14; L20; L25 ].
Definition S21 := [ L2; L10; L16; L19; L24 ].
Definition S22 := [ L2; L11; L13; L20; L23 ].
Definition S23 := [ L2; L11; L18; L19; L26 ].
Definition S24 := [ L3; L7; L14; L21; L30 ].
Definition S25 := [ L3; L7; L16; L19; L29 ].
Definition S26 := [ L3; L9; L15; L25; L29 ].
Definition S27 := [ L3; L9; L17; L21; L34 ].
Definition S28 := [ L3; L11; L15; L23; L30 ].
Definition S29 := [ L3; L11; L17; L19; L33 ].
Definition S30 := [ L3; L12; L14; L25; L33 ].
Definition S31 := [ L3; L12; L16; L23; L34 ].
Definition S32 := [ L4; L7; L14; L20; L28 ].
Definition S33 := [ L4; L7; L16; L22; L27 ].
Definition S34 := [ L4; L9; L15; L24; L28 ].
Definition S35 := [ L4; L9; L17; L22; L32 ].
Definition S36 := [ L4; L11; L15; L26; L27 ].
Definition S37 := [ L4; L11; L17; L20; L31 ].
Definition S38 := [ L4; L12; L14; L26; L32 ].
Definition S39 := [ L4; L12; L16; L24; L31 ].
Definition S40 := [ L5; L7; L13; L21; L27 ].
Definition S41 := [ L5; L7; L18; L19; L28 ].
Definition S42 := [ L5; L8; L15; L23; L28 ].
Definition S43 := [ L5; L8; L17; L21; L31 ].
Definition S44 := [ L5; L10; L15; L25; L27 ].
Definition S45 := [ L5; L10; L17; L19; L32 ].
Definition S46 := [ L5; L12; L13; L23; L32 ].
Definition S47 := [ L5; L12; L18; L25; L31 ].
Definition S48 := [ L6; L7; L13; L20; L29 ].
Definition S49 := [ L6; L7; L18; L22; L30 ].
Definition S50 := [ L6; L8; L15; L26; L29 ].
Definition S51 := [ L6; L8; L17; L22; L33 ].
Definition S52 := [ L6; L10; L15; L24; L30 ].
Definition S53 := [ L6; L10; L17; L20; L34 ].
Definition S54 := [ L6; L12; L13; L24; L33 ].
Definition S55 := [ L6; L12; L18; L26; L34 ].

Definition spreads := [ S0 ; S1 ; S2 ; S3 ; S4 ; S5 ; S6 ; S7 ; S8 ; S9 ; S10 ; S11 ; S12 ; S13 ; S14 ; S15 ; S16 ; S17 ; S18 ; S19 ; S20 ; S21 ; S22 ; S23 ; S24 ; S25 ; S26 ; S27 ; S28 ; S29 ; S30 ; S31 ; S32 ; S33 ; S34 ; S35 ; S36 ; S37 ; S38 ; S39 ; S40 ; S41 ; S42 ; S43 ; S44 ; S45 ; S46 ; S47 ; S48 ; S49 ; S50 ; S51 ; S52 ; S53 ; S54 ; S55 ].

Definition PA0 := [ S0; S9; S19; S24; S36; S46; S53 ].
Definition PA1 := [ S0; S9; S19; S28; S38; S40; S53 ].
Definition PA2 := [ S0; S9; S20; S27; S36; S46; S49 ].
Definition PA3 := [ S0; S9; S20; S28; S35; S40; S55 ].
Definition PA4 := [ S0; S9; S22; S24; S35; S44; S55 ].
Definition PA5 := [ S0; S9; S22; S27; S38; S44; S49 ].
Definition PA6 := [ S0; S10; S16; S28; S33; S47; S53 ].
Definition PA7 := [ S0; S10; S16; S31; S37; S44; S49 ].
Definition PA8 := [ S0; S10; S17; S24; S36; S47; S53 ].
Definition PA9 := [ S0; S10; S17; S24; S37; S44; S55 ].
Definition PA10 := [ S0; S10; S20; S28; S33; S43; S55 ].
Definition PA11 := [ S0; S10; S20; S31; S36; S43; S49 ].
Definition PA12 := [ S0; S12; S17; S26; S37; S40; S55 ].
Definition PA13 := [ S0; S12; S17; S27; S36; S47; S48 ].
Definition PA14 := [ S0; S12; S19; S31; S36; S43; S48 ].
Definition PA15 := [ S0; S12; S19; S31; S37; S40; S50 ].
Definition PA16 := [ S0; S12; S22; S26; S33; S43; S55 ].
Definition PA17 := [ S0; S12; S22; S27; S33; S47; S50 ].
Definition PA18 := [ S0; S13; S16; S26; S37; S46; S49 ].
Definition PA19 := [ S0; S13; S16; S28; S35; S47; S48 ].
Definition PA20 := [ S0; S13; S19; S24; S37; S46; S50 ].
Definition PA21 := [ S0; S13; S19; S28; S38; S43; S48 ].
Definition PA22 := [ S0; S13; S22; S24; S35; S47; S50 ].
Definition PA23 := [ S0; S13; S22; S26; S38; S43; S49 ].
Definition PA24 := [ S0; S15; S16; S26; S33; S46; S53 ].
Definition PA25 := [ S0; S15; S16; S31; S35; S44; S48 ].
Definition PA26 := [ S0; S15; S17; S26; S38; S40; S53 ].
Definition PA27 := [ S0; S15; S17; S27; S38; S44; S48 ].
Definition PA28 := [ S0; S15; S20; S27; S33; S46; S50 ].
Definition PA29 := [ S0; S15; S20; S31; S35; S40; S50 ].
Definition PA30 := [ S1; S8; S18; S28; S33; S47; S53 ].
Definition PA31 := [ S1; S8; S18; S31; S37; S44; S49 ].
Definition PA32 := [ S1; S8; S19; S28; S39; S40; S53 ].
Definition PA33 := [ S1; S8; S19; S31; S37; S40; S52 ].
Definition PA34 := [ S1; S8; S22; S27; S33; S47; S52 ].
Definition PA35 := [ S1; S8; S22; S27; S39; S44; S49 ].
Definition PA36 := [ S1; S11; S17; S24; S37; S44; S54 ].
Definition PA37 := [ S1; S11; S17; S30; S37; S40; S52 ].
Definition PA38 := [ S1; S11; S20; S28; S33; S43; S54 ].
Definition PA39 := [ S1; S11; S20; S28; S39; S40; S51 ].
Definition PA40 := [ S1; S11; S22; S24; S39; S44; S51 ].
Definition PA41 := [ S1; S11; S22; S30; S33; S43; S52 ].
Definition PA42 := [ S1; S13; S18; S28; S32; S47; S51 ].
Definition PA43 := [ S1; S13; S18; S30; S37; S42; S49 ].
Definition PA44 := [ S1; S13; S19; S24; S37; S42; S54 ].
Definition PA45 := [ S1; S13; S19; S28; S32; S43; S54 ].
Definition PA46 := [ S1; S13; S22; S24; S34; S47; S51 ].
Definition PA47 := [ S1; S13; S22; S30; S34; S43; S49 ].
Definition PA48 := [ S1; S14; S17; S24; S34; S47; S53 ].
Definition PA49 := [ S1; S14; S17; S27; S32; S47; S52 ].
Definition PA50 := [ S1; S14; S19; S24; S39; S42; S53 ].
Definition PA51 := [ S1; S14; S19; S31; S32; S43; S52 ].
Definition PA52 := [ S1; S14; S20; S27; S39; S42; S49 ].
Definition PA53 := [ S1; S14; S20; S31; S34; S43; S49 ].
Definition PA54 := [ S1; S15; S17; S27; S32; S44; S54 ].
Definition PA55 := [ S1; S15; S17; S30; S34; S40; S53 ].
Definition PA56 := [ S1; S15; S18; S30; S33; S42; S53 ].
Definition PA57 := [ S1; S15; S18; S31; S32; S44; S51 ].
Definition PA58 := [ S1; S15; S20; S27; S33; S42; S54 ].
Definition PA59 := [ S1; S15; S20; S31; S34; S40; S51 ].
Definition PA60 := [ S2; S9; S18; S29; S38; S44; S49 ].
Definition PA61 := [ S2; S9; S18; S30; S36; S45; S49 ].
Definition PA62 := [ S2; S9; S19; S24; S36; S45; S54 ].
Definition PA63 := [ S2; S9; S19; S29; S38; S40; S52 ].
Definition PA64 := [ S2; S9; S23; S24; S35; S44; S54 ].
Definition PA65 := [ S2; S9; S23; S30; S35; S40; S52 ].
Definition PA66 := [ S2; S10; S16; S29; S33; S47; S52 ].
Definition PA67 := [ S2; S10; S16; S29; S39; S44; S49 ].
Definition PA68 := [ S2; S10; S21; S24; S36; S47; S51 ].
Definition PA69 := [ S2; S10; S21; S30; S36; S43; S49 ].
Definition PA70 := [ S2; S10; S23; S24; S39; S44; S51 ].
Definition PA71 := [ S2; S10; S23; S30; S33; S43; S52 ].
Definition PA72 := [ S2; S12; S18; S25; S36; S47; S51 ].
Definition PA73 := [ S2; S12; S18; S29; S33; S47; S50 ].
Definition PA74 := [ S2; S12; S19; S25; S36; S43; S54 ].
Definition PA75 := [ S2; S12; S19; S29; S39; S40; S50 ].
Definition PA76 := [ S2; S12; S23; S26; S33; S43; S54 ].
Definition PA77 := [ S2; S12; S23; S26; S39; S40; S51 ].
Definition PA78 := [ S2; S14; S16; S25; S35; S47; S52 ].
Definition PA79 := [ S2; S14; S16; S26; S39; S45; S49 ].
Definition PA80 := [ S2; S14; S19; S24; S39; S45; S50 ].
Definition PA81 := [ S2; S14; S19; S25; S38; S43; S52 ].
Definition PA82 := [ S2; S14; S21; S24; S35; S47; S50 ].
Definition PA83 := [ S2; S14; S21; S26; S38; S43; S49 ].
Definition PA84 := [ S2; S15; S16; S25; S35; S44; S54 ].
Definition PA85 := [ S2; S15; S16; S26; S33; S45; S54 ].
Definition PA86 := [ S2; S15; S18; S25; S38; S44; S51 ].
Definition PA87 := [ S2; S15; S18; S30; S33; S45; S50 ].
Definition PA88 := [ S2; S15; S21; S26; S38; S40; S51 ].
Definition PA89 := [ S2; S15; S21; S30; S35; S40; S50 ].
Definition PA90 := [ S3; S8; S18; S28; S33; S45; S55 ].
Definition PA91 := [ S3; S8; S18; S31; S36; S45; S49 ].
Definition PA92 := [ S3; S8; S21; S27; S36; S46; S49 ].
Definition PA93 := [ S3; S8; S21; S28; S35; S40; S55 ].
Definition PA94 := [ S3; S8; S23; S27; S33; S46; S52 ].
Definition PA95 := [ S3; S8; S23; S31; S35; S40; S52 ].
Definition PA96 := [ S3; S11; S16; S28; S33; S45; S54 ].
Definition PA97 := [ S3; S11; S16; S29; S33; S46; S52 ].
Definition PA98 := [ S3; S11; S17; S24; S36; S45; S54 ].
Definition PA99 := [ S3; S11; S17; S29; S38; S40; S52 ].
Definition PA100 := [ S3; S11; S21; S24; S36; S46; S51 ].
Definition PA101 := [ S3; S11; S21; S28; S38; S40; S51 ].
Definition PA102 := [ S3; S12; S17; S27; S36; S41; S54 ].
Definition PA103 := [ S3; S12; S17; S29; S34; S40; S55 ].
Definition PA104 := [ S3; S12; S18; S29; S33; S42; S55 ].
Definition PA105 := [ S3; S12; S18; S31; S36; S41; S51 ].
Definition PA106 := [ S3; S12; S23; S27; S33; S42; S54 ].
Definition PA107 := [ S3; S12; S23; S31; S34; S40; S51 ].
Definition PA108 := [ S3; S13; S16; S28; S35; S41; S54 ].
Definition PA109 := [ S3; S13; S16; S29; S34; S46; S49 ].
Definition PA110 := [ S3; S13; S18; S28; S38; S41; S51 ].
Definition PA111 := [ S3; S13; S18; S29; S38; S42; S49 ].
Definition PA112 := [ S3; S13; S23; S24; S34; S46; S51 ].
Definition PA113 := [ S3; S13; S23; S24; S35; S42; S54 ].
Definition PA114 := [ S3; S14; S16; S31; S34; S45; S49 ].
Definition PA115 := [ S3; S14; S16; S31; S35; S41; S52 ].
Definition PA116 := [ S3; S14; S17; S24; S34; S45; S55 ].
Definition PA117 := [ S3; S14; S17; S27; S38; S41; S52 ].
Definition PA118 := [ S3; S14; S21; S24; S35; S42; S55 ].
Definition PA119 := [ S3; S14; S21; S27; S38; S42; S49 ].
Definition PA120 := [ S4; S8; S19; S25; S36; S46; S53 ].
Definition PA121 := [ S4; S8; S19; S31; S36; S45; S48 ].
Definition PA122 := [ S4; S8; S22; S25; S35; S44; S55 ].
Definition PA123 := [ S4; S8; S22; S26; S33; S45; S55 ].
Definition PA124 := [ S4; S8; S23; S26; S33; S46; S53 ].
Definition PA125 := [ S4; S8; S23; S31; S35; S44; S48 ].
Definition PA126 := [ S4; S10; S17; S29; S32; S44; S55 ].
Definition PA127 := [ S4; S10; S17; S30; S36; S41; S53 ].
Definition PA128 := [ S4; S10; S20; S29; S33; S42; S55 ].
Definition PA129 := [ S4; S10; S20; S31; S36; S41; S51 ].
Definition PA130 := [ S4; S10; S23; S30; S33; S42; S53 ].
Definition PA131 := [ S4; S10; S23; S31; S32; S44; S51 ].
Definition PA132 := [ S4; S11; S17; S29; S38; S44; S48 ].
Definition PA133 := [ S4; S11; S17; S30; S36; S45; S48 ].
Definition PA134 := [ S4; S11; S20; S25; S36; S46; S51 ].
Definition PA135 := [ S4; S11; S20; S29; S33; S46; S50 ].
Definition PA136 := [ S4; S11; S22; S25; S38; S44; S51 ].
Definition PA137 := [ S4; S11; S22; S30; S33; S45; S50 ].
Definition PA138 := [ S4; S13; S19; S29; S32; S46; S50 ].
Definition PA139 := [ S4; S13; S19; S29; S38; S42; S48 ].
Definition PA140 := [ S4; S13; S22; S26; S38; S41; S51 ].
Definition PA141 := [ S4; S13; S22; S30; S35; S41; S50 ].
Definition PA142 := [ S4; S13; S23; S26; S32; S46; S51 ].
Definition PA143 := [ S4; S13; S23; S30; S35; S42; S48 ].
Definition PA144 := [ S4; S14; S17; S26; S32; S45; S55 ].
Definition PA145 := [ S4; S14; S17; S26; S38; S41; S53 ].
Definition PA146 := [ S4; S14; S19; S25; S38; S42; S53 ].
Definition PA147 := [ S4; S14; S19; S31; S32; S45; S50 ].
Definition PA148 := [ S4; S14; S20; S25; S35; S42; S55 ].
Definition PA149 := [ S4; S14; S20; S31; S35; S41; S50 ].
Definition PA150 := [ S5; S8; S19; S25; S37; S46; S52 ].
Definition PA151 := [ S5; S8; S19; S28; S39; S45; S48 ].
Definition PA152 := [ S5; S8; S21; S26; S37; S46; S49 ].
Definition PA153 := [ S5; S8; S21; S28; S35; S47; S48 ].
Definition PA154 := [ S5; S8; S22; S25; S35; S47; S52 ].
Definition PA155 := [ S5; S8; S22; S26; S39; S45; S49 ].
Definition PA156 := [ S5; S9; S19; S28; S32; S45; S54 ].
Definition PA157 := [ S5; S9; S19; S29; S32; S46; S52 ].
Definition PA158 := [ S5; S9; S20; S28; S35; S41; S54 ].
Definition PA159 := [ S5; S9; S20; S29; S34; S46; S49 ].
Definition PA160 := [ S5; S9; S22; S30; S34; S45; S49 ].
Definition PA161 := [ S5; S9; S22; S30; S35; S41; S52 ].
Definition PA162 := [ S5; S10; S17; S29; S32; S47; S52 ].
Definition PA163 := [ S5; S10; S17; S30; S37; S41; S52 ].
Definition PA164 := [ S5; S10; S20; S28; S39; S41; S51 ].
Definition PA165 := [ S5; S10; S20; S29; S39; S42; S49 ].
Definition PA166 := [ S5; S10; S21; S28; S32; S47; S51 ].
Definition PA167 := [ S5; S10; S21; S30; S37; S42; S49 ].
Definition PA168 := [ S5; S12; S17; S26; S37; S41; S54 ].
Definition PA169 := [ S5; S12; S17; S29; S34; S47; S48 ].
Definition PA170 := [ S5; S12; S19; S25; S37; S42; S54 ].
Definition PA171 := [ S5; S12; S19; S29; S39; S42; S48 ].
Definition PA172 := [ S5; S12; S22; S25; S34; S47; S51 ].
Definition PA173 := [ S5; S12; S22; S26; S39; S41; S51 ].
Definition PA174 := [ S5; S15; S17; S26; S32; S45; S54 ].
Definition PA175 := [ S5; S15; S17; S30; S34; S45; S48 ].
Definition PA176 := [ S5; S15; S20; S25; S34; S46; S51 ].
Definition PA177 := [ S5; S15; S20; S25; S35; S42; S54 ].
Definition PA178 := [ S5; S15; S21; S26; S32; S46; S51 ].
Definition PA179 := [ S5; S15; S21; S30; S35; S42; S48 ].
Definition PA180 := [ S6; S8; S18; S25; S36; S47; S53 ].
Definition PA181 := [ S6; S8; S18; S25; S37; S44; S55 ].
Definition PA182 := [ S6; S8; S21; S26; S37; S40; S55 ].
Definition PA183 := [ S6; S8; S21; S27; S36; S47; S48 ].
Definition PA184 := [ S6; S8; S23; S26; S39; S40; S53 ].
Definition PA185 := [ S6; S8; S23; S27; S39; S44; S48 ].
Definition PA186 := [ S6; S9; S18; S29; S32; S44; S55 ].
Definition PA187 := [ S6; S9; S18; S30; S36; S41; S53 ].
Definition PA188 := [ S6; S9; S20; S27; S36; S41; S54 ].
Definition PA189 := [ S6; S9; S20; S29; S34; S40; S55 ].
Definition PA190 := [ S6; S9; S23; S27; S32; S44; S54 ].
Definition PA191 := [ S6; S9; S23; S30; S34; S40; S53 ].
Definition PA192 := [ S6; S11; S16; S25; S37; S44; S54 ].
Definition PA193 := [ S6; S11; S16; S29; S39; S44; S48 ].
Definition PA194 := [ S6; S11; S20; S25; S36; S43; S54 ].
Definition PA195 := [ S6; S11; S20; S29; S39; S40; S50 ].
Definition PA196 := [ S6; S11; S21; S30; S36; S43; S48 ].
Definition PA197 := [ S6; S11; S21; S30; S37; S40; S50 ].
Definition PA198 := [ S6; S13; S16; S26; S37; S41; S54 ].
Definition PA199 := [ S6; S13; S16; S29; S34; S47; S48 ].
Definition PA200 := [ S6; S13; S18; S29; S32; S47; S50 ].
Definition PA201 := [ S6; S13; S18; S30; S37; S41; S50 ].
Definition PA202 := [ S6; S13; S23; S26; S32; S43; S54 ].
Definition PA203 := [ S6; S13; S23; S30; S34; S43; S48 ].
Definition PA204 := [ S6; S14; S16; S25; S34; S47; S53 ].
Definition PA205 := [ S6; S14; S16; S26; S39; S41; S53 ].
Definition PA206 := [ S6; S14; S20; S25; S34; S43; S55 ].
Definition PA207 := [ S6; S14; S20; S27; S39; S41; S50 ].
Definition PA208 := [ S6; S14; S21; S26; S32; S43; S55 ].
Definition PA209 := [ S6; S14; S21; S27; S32; S47; S50 ].
Definition PA210 := [ S7; S9; S18; S28; S32; S45; S55 ].
Definition PA211 := [ S7; S9; S18; S28; S38; S41; S53 ].
Definition PA212 := [ S7; S9; S22; S24; S34; S45; S55 ].
Definition PA213 := [ S7; S9; S22; S27; S38; S41; S52 ].
Definition PA214 := [ S7; S9; S23; S24; S34; S46; S53 ].
Definition PA215 := [ S7; S9; S23; S27; S32; S46; S52 ].
Definition PA216 := [ S7; S10; S16; S28; S39; S41; S53 ].
Definition PA217 := [ S7; S10; S16; S31; S37; S41; S52 ].
Definition PA218 := [ S7; S10; S21; S24; S37; S42; S55 ].
Definition PA219 := [ S7; S10; S21; S28; S32; S43; S55 ].
Definition PA220 := [ S7; S10; S23; S24; S39; S42; S53 ].
Definition PA221 := [ S7; S10; S23; S31; S32; S43; S52 ].
Definition PA222 := [ S7; S11; S16; S25; S37; S46; S52 ].
Definition PA223 := [ S7; S11; S16; S28; S39; S45; S48 ].
Definition PA224 := [ S7; S11; S21; S24; S37; S46; S50 ].
Definition PA225 := [ S7; S11; S21; S28; S38; S43; S48 ].
Definition PA226 := [ S7; S11; S22; S24; S39; S45; S50 ].
Definition PA227 := [ S7; S11; S22; S25; S38; S43; S52 ].
Definition PA228 := [ S7; S12; S18; S25; S37; S42; S55 ].
Definition PA229 := [ S7; S12; S18; S31; S37; S41; S50 ].
Definition PA230 := [ S7; S12; S22; S25; S34; S43; S55 ].
Definition PA231 := [ S7; S12; S22; S27; S39; S41; S50 ].
Definition PA232 := [ S7; S12; S23; S27; S39; S42; S48 ].
Definition PA233 := [ S7; S12; S23; S31; S34; S43; S48 ].
Definition PA234 := [ S7; S15; S16; S25; S34; S46; S53 ].
Definition PA235 := [ S7; S15; S16; S31; S34; S45; S48 ].
Definition PA236 := [ S7; S15; S18; S25; S38; S42; S53 ].
Definition PA237 := [ S7; S15; S18; S31; S32; S45; S50 ].
Definition PA238 := [ S7; S15; S21; S27; S32; S46; S50 ].
Definition PA239 := [ S7; S15; S21; S27; S38; S42; S48 ].

Definition packings := [ PA0 ; PA1 ; PA2 ; PA3 ; PA4 ; PA5 ; PA6 ; PA7 ; PA8 ; PA9 ; PA10 ; PA11 ; PA12 ; PA13 ; PA14 ; PA15 ; PA16 ; PA17 ; PA18 ; PA19 ; PA20 ; PA21 ; PA22 ; PA23 ; PA24 ; PA25 ; PA26 ; PA27 ; PA28 ; PA29 ; PA30 ; PA31 ; PA32 ; PA33 ; PA34 ; PA35 ; PA36 ; PA37 ; PA38 ; PA39 ; PA40 ; PA41 ; PA42 ; PA43 ; PA44 ; PA45 ; PA46 ; PA47 ; PA48 ; PA49 ; PA50 ; PA51 ; PA52 ; PA53 ; PA54 ; PA55 ; PA56 ; PA57 ; PA58 ; PA59 ; PA60 ; PA61 ; PA62 ; PA63 ; PA64 ; PA65 ; PA66 ; PA67 ; PA68 ; PA69 ; PA70 ; PA71 ; PA72 ; PA73 ; PA74 ; PA75 ; PA76 ; PA77 ; PA78 ; PA79 ; PA80 ; PA81 ; PA82 ; PA83 ; PA84 ; PA85 ; PA86 ; PA87 ; PA88 ; PA89 ; PA90 ; PA91 ; PA92 ; PA93 ; PA94 ; PA95 ; PA96 ; PA97 ; PA98 ; PA99 ; PA100 ; PA101 ; PA102 ; PA103 ; PA104 ; PA105 ; PA106 ; PA107 ; PA108 ; PA109 ; PA110 ; PA111 ; PA112 ; PA113 ; PA114 ; PA115 ; PA116 ; PA117 ; PA118 ; PA119 ; PA120 ; PA121 ; PA122 ; PA123 ; PA124 ; PA125 ; PA126 ; PA127 ; PA128 ; PA129 ; PA130 ; PA131 ; PA132 ; PA133 ; PA134 ; PA135 ; PA136 ; PA137 ; PA138 ; PA139 ; PA140 ; PA141 ; PA142 ; PA143 ; PA144 ; PA145 ; PA146 ; PA147 ; PA148 ; PA149 ; PA150 ; PA151 ; PA152 ; PA153 ; PA154 ; PA155 ; PA156 ; PA157 ; PA158 ; PA159 ; PA160 ; PA161 ; PA162 ; PA163 ; PA164 ; PA165 ; PA166 ; PA167 ; PA168 ; PA169 ; PA170 ; PA171 ; PA172 ; PA173 ; PA174 ; PA175 ; PA176 ; PA177 ; PA178 ; PA179 ; PA180 ; PA181 ; PA182 ; PA183 ; PA184 ; PA185 ; PA186 ; PA187 ; PA188 ; PA189 ; PA190 ; PA191 ; PA192 ; PA193 ; PA194 ; PA195 ; PA196 ; PA197 ; PA198 ; PA199 ; PA200 ; PA201 ; PA202 ; PA203 ; PA204 ; PA205 ; PA206 ; PA207 ; PA208 ; PA209 ; PA210 ; PA211 ; PA212 ; PA213 ; PA214 ; PA215 ; PA216 ; PA217 ; PA218 ; PA219 ; PA220 ; PA221 ; PA222 ; PA223 ; PA224 ; PA225 ; PA226 ; PA227 ; PA228 ; PA229 ; PA230 ; PA231 ; PA232 ; PA233 ; PA234 ; PA235 ; PA236 ; PA237 ; PA238 ; PA239 ].

Definition class0 := [].
