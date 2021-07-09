namespace AuthEd25519


open System
open System.Diagnostics
open System.Security.Cryptography
open System.Text
open Chaos.NaCl
open Konscious.Security.Cryptography
open Newtonsoft.Json
module AuthEd25519 =
[<JsonObject(MemberSerialization = MemberSerialization.Fields)>]
type PrivateKey = private PrivateKey of byte [] with
    member this.string = match this with PrivateKey p -> Convert.ToBase64String p
    member this.bytes = match this with PrivateKey p -> p |> Array.copy
[<JsonObject(MemberSerialization = MemberSerialization.Fields)>]
type PublicKey = private PublicKey of byte [] with
    member this.string = match this with PublicKey p -> Convert.ToBase64String p
    member this.bytes = match this with PublicKey p -> p |> Array.copy
[<JsonObject(MemberSerialization = MemberSerialization.Fields)>]
type Signature = private Signature of byte [] with
    member this.string = match this with Signature p -> Convert.ToBase64String p
    member this.bytes = match this with Signature p -> p |> Array.copy
[<JsonObject(MemberSerialization = MemberSerialization.Fields)>]
type Seed = private Seed of byte [] with
    member this.string = match this with Seed p -> Convert.ToBase64String p
    member this.bytes = match this with Seed p -> p |> Array.copy

let rand = RNGCryptoServiceProvider.Create()
let empty_seed() = Seed <| Array.init 32 (fun _ -> 0uy)

let bpub, bpriv, bseed = PublicKey, PrivateKey, Seed
let spub (s:string) = Convert.FromBase64String s |> bpub
let spriv (s:string) = Convert.FromBase64String s |> bpriv
let sseed (s:string) = Convert.FromBase64String s |> bseed

let load_pub_priv_from_strings pub priv = spub pub, spriv priv
let load_pub_priv_from_seed (Seed seed) =
    let pub, priv = ref (Array.init 32 (fun _ -> 0uy)), ref <| Array.init 64 (fun _ -> 0uy)
    Ed25519.KeyPairFromSeed (pub, priv, seed)
    PublicKey !pub, PrivateKey !priv
let mk_seed () = let seed = empty_seed().bytes in let _ = rand.GetBytes seed in Seed seed
let mk_seed_pub_priv () = let seed = mk_seed() in seed, load_pub_priv_from_seed seed
let mk_sign ps (msg:string) =
    let sigs = ps |> List.map (fun  (PrivateKey p) ->
        let data = Encoding.UTF8.GetBytes msg
        let signature = Ed25519.Sign(data, p)
        Signature signature)
    msg, sigs
let mk_verifier (ps:PublicKey list) (msg:string, signatures) =
    let data = Encoding.UTF8.GetBytes msg
    if ps |> List.exists (fun (PublicKey p) -> signatures |> List.exists (fun (Signature signature) -> Ed25519.Verify(signature, data, p)))
    then Ok msg
    else Error <| sprintf "Signature Verification Failed: pubs: %A; msg: %s;" ps msg
let combine_signatures (t, ss) (t2, ss2) = if t = t2 then t, List.append ss ss2 else t, ss
type Account = {pub: PublicKey; priv: PrivateKey;}
    with
    member acc.sign = mk_sign [acc.priv]
let new_account () = let seed, (pub, priv) = mk_seed_pub_priv () in seed, {pub = pub; priv = priv}
let bload_account pub priv = {pub=pub; priv=priv}
let sload_account pub priv = bload_account <|| load_pub_priv_from_strings pub priv
let bload_account_seed seed = load_pub_priv_from_seed seed ||> bload_account
let sload_account_seed seed = sseed seed |> load_pub_priv_from_seed ||> bload_account

let argon2hash iterations memory_size degrees_of_parallelism size known_secret extra salt pass =
    let arg = Argon2id pass
    arg.Iterations <- iterations
    arg.Salt
    arg.AssociatedData <- extra
    arg.KnownSecret <- known_secret
    arg.MemorySize <- memory_size
    arg.DegreeOfParallelism <- degrees_of_parallelism
    arg.GetBytes size
let def_iterations = 6L
let def_memory_size = 2_000_000L
let def_degree_of_parallelism = 2L
let strength x = (Zxcvbn.Core.EvaluatePassword x).Score |> int64

let rec private tails = function [] -> [] | (x::xs) as vs -> let rest = tails xs in if rest = [[]] then [vs] else vs::rest
let rec private inits = function [] -> [] | xs -> let init = List.take (xs.Length - 1) xs in let rest = inits init in (if rest = [[]] then [xs] else xs::rest)
let private sublists x = x |> (tails >> List.collect (List.tail << inits))
let private substrings = List.ofSeq >> sublists >> List.map (fun x -> new string(List.toArray x))

let max_strength = 1200L
let rstrength (pass:string) =substrings pass |> List.sumBy strength |> ((*)2L) |> fun x -> if x > max_strength then max_strength else x
let rweakness pass = max_strength - rstrength pass


let shasherino known_secret (extra:string) (salt:string) (pass:string) =
    let weakness = rweakness pass
    let known_secret = Convert.FromBase64String known_secret
    let salt = Encoding.UTF8.GetBytes salt
    let extra = Encoding.UTF8.GetBytes extra
    let pass = Encoding.UTF8.GetBytes pass
    let harden min = fun x -> let m = (x*weakness)/max_strength in if m < min then (*let _ = printfn "here %A" (x, weakness,x*weakness, max_strength, m, min) in*) min else m
    let its = int32 <| harden 3L def_iterations
    let m = int32 <| harden 100_000L def_memory_size
    let d = int32 <| def_degree_of_parallelism
    argon2hash its m d 32 known_secret salt extra pass
let load_acc_from_details known_secret extra salt pass = shasherino known_secret extra salt pass |> bseed |> fun s -> s, bload_account_seed s
let bench f =
    let t = Stopwatch.StartNew()
    let ret = f()
    ret, t.ElapsedMilliseconds
