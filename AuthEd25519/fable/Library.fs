﻿module AuthEd25519


open System
open System.Diagnostics
open System.Security.Cryptography
open System.Text
open Konscious.Security.Cryptography
open Newtonsoft.Json
//module AuthEd25519 =
open TezFs open Netezos open Netezos.Keys

[<JsonObject(MemberSerialization = MemberSerialization.Fields)>]
type PrivateKey = private PrivateKey of Key with
    member this.string = match this with PrivateKey p -> p.GetBase58()
    member this.bytes = match this with PrivateKey p -> p.GetBytes()
[<JsonObject(MemberSerialization = MemberSerialization.Fields)>]
type PublicKey = private PublicKey of PubKey with
    member this.string = match this with PublicKey p -> p.GetBase58()
    member this.bytes = match this with PublicKey p -> p.GetBytes()
[<JsonObject(MemberSerialization = MemberSerialization.Fields)>]
type Signature = private Signature of Netezos.Keys.Signature with
    member this.string = match this with Signature p -> p.ToBase58()
    member this.bytes = match this with Signature p -> p.ToBytes()


let spriv (s:string) = acc_base58 s

let mk_sign ps (msg:string) =
    let sigs = ps |> List.map (fun  (PrivateKey p) ->
        let signature = p.Sign(msg)
        Signature signature)
    msg, sigs
let mk_verifier (ps:PublicKey list) (msg:string, signatures) =
    if ps |> List.exists (fun (PublicKey p) -> signatures |> List.exists (fun (Signature signature) -> p.Verify(msg, signature.ToBase58())))
    then Ok msg
    else Error <| sprintf "Signature Verification Failed: pubs: %A; msg: %s;" ps msg
let combine_signatures (t, ss) (t2, ss2) = if t = t2 then t, List.append ss ss2 else t, ss
[<JsonObject(MemberSerialization = MemberSerialization.Fields)>]
type Account = private {priv: PrivateKey;}
    with
    member acc.pub = match acc.priv with PrivateKey p -> PublicKey p.PubKey
    member acc.pub_hash = match acc.priv with PrivateKey p -> p.PubKey.Address
    member acc.sign = mk_sign [acc.priv]
let new_account () = random_account ()

let argon2hash iterations memory_size degrees_of_parallelism size known_secret extra salt pass =
    let arg = new Argon2id(pass)
    arg.Iterations <- iterations
    arg.Salt <- salt
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
    let harden min = fun x -> let m = (x*weakness)/max_strength in max m min
    let its = int32 <| harden 1L def_iterations
    let m = int32 <| harden 100_000L def_memory_size + weakness
    let d = int32 <| def_degree_of_parallelism
    argon2hash its m d 32 known_secret salt extra pass
let load_acc_from_details known_secret extra salt pass = shasherino known_secret extra salt pass |> Key.FromBytes |> fun k -> {priv = PrivateKey k}
let memory_login name pass = load_acc_from_details "be5d9f66cf2ebed67f5a3c68ce69bd07a1ecad2b88db7cfaf5ac63aba8eaf6fe" "hog"
let bench f =
    let t = Stopwatch.StartNew()
    let ret = f()
    ret, t.ElapsedMilliseconds
