# idris2-extra
My personal library for idris2

This is library exists since usually I can't find what I need from the base/contrib/network/prelude library as the `:search` REPL command is still under development. I may be reinventing the wheel unknowingly.

Once TLS and HTTP are implemented, I will be porting `tensorknower69/nhentai` and other stuff to Idris2 asap since they are *useful*.

PRs are welcomed!!!!!111111 If any..., I mean Idris2 is still not well-known yet. How do I make friends in/at/on school

## TODO List (The percentages are completely arbitrary):
- HTML
  - 0%: Parser // [tagsoup](https://hackage.haskell.org/package/tagsoup)
  - 0%: Decoder // [Scalpel](https://hackage.haskell.org/package/scalpel-core)
- HTTP
  - 0%: Parser
  - 0%: Client
- 50%: Linear networking
- [GPipe](https://hackage.haskell.org/package/GPipe)
  - 0%: OpenGL
  - [GPipe-GLFW](https://hackage.haskell.org/package/GPipe-GLFW)
    - 0%: GLFW
- 0.01% : OpenSSL
- JSON
  - 100%: Parser
  - 0%: Encoder
  - 0%: Decoder
- 0%: TLS 
- Incremental parser
  - 100%: Core
  - 0%: Error reporting
- Whatever can be found on the python/haskell package index. I may choose Idris2 as my primary language for side projects. Currently, I don't mind if stuff is unsafe or wacky, I just want to be able to write an application first. In the future, I will take this more seriously.

## Questions I have and I am afraid to ask (unmaintained)

- How do I rewrite linear values with `rewrite` `in` syntax (Idris 2, version 0.3.0-1d96dd2bd)

  Currently I am using `rewrite1` from `Extra.Proof`. This problem has plagued `Extra.Bytes`. I'm having the vibe that `rewrite` on linear values is violating fundamental logic.
  
- Why `String` with `\0` behaves so weirdly (Idris 2, version 0.3.0-1d96dd2bd)

  When doing `recv` using `Network.Socket` with sockets and the received message contains a null char, the length of the resultant String is up to the first null char. Is this a bug?
  
- Why use `Int` in unseemingly inappropriate situations? Or there are reasons for doing that (Idris 2, version 0.3.0-1d96dd2bd)

  Ex. `Data.Buffer.bufferData : HasIO io => Buffer -> io (List Int)` 
  Shouldn't it be `bufferData : HasIO io => Buffer -> io (List Bits8)`?

- Is there a more elegant way to deal with lazyness of `Applicative`, `Alternative` and more  (Idris 2, version 0.3.0-1d96dd2bd)

  See `Extra.Parser`. There are situations where applicatives with laziness must be used or otherwise the program will halt at compiletime/runtime. But according to https://github.com/idris-lang/Idris2/pull/867, it seems as if having designated interfaces isn't the answer. I'm puzzled.

- Incomplete ipkg implementation?

  I need fields like `makefile` and `objs` to install `libextra.so`
