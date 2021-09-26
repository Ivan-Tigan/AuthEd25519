open MBrace.FsPickler
type Sig(x) =
    member private this.x : byte [] = x
[<EntryPoint>]
let main argv =
    let reg = CustomPicklerRegistry()
    let cache = PicklerCache.FromCustomPicklerRegistry reg
    let ser = FsPickler.CreateBinarySerializer(picklerResolver = cache)
    reg.RegisterFactory AuthEd25519.Signature.CreatePickler
    let a1 = AuthEd25519.new_account()
    let s1 = a1.sign "Hello" |> snd |> List.head
    let s = FsPickler.CreateBinarySerializer()
    let _ = s.Pickle a1.pub
    printfn "%A" argv
    0 // return an integer exit code
