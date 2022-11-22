(* Notes and note transformations *)
(* Compared to IBAL, we are able to  express the transformations much more
   concisely, thank to the richness of the host language.
*)

type note = A | Asharp | B | C | Csharp | D | Dsharp | E | F | Fsharp | G | Gsharp

let string_of_note = function
  | A -> "A" | Asharp -> "A#" | B -> "B" | C -> "C" | Csharp -> "C#" | D -> "D"
  | Dsharp -> "D#" | E -> "E" | F -> "F" | Fsharp -> "F#" | G -> "G" | Gsharp ->
      "G#"

let octave  = [A; Asharp; B; C; Csharp; D; Dsharp; E; F; Fsharp; G; Gsharp;
	       A; Asharp; B; C; Csharp; D; Dsharp; E; F; Fsharp; G; Gsharp;
	       A; Asharp; B; C; Csharp; D; Dsharp; E; F; Fsharp; G; Gsharp]

let note_to_int = function
  | A      -> 0
  | Asharp -> 1
  | B      -> 2
  | C      -> 3
  | Csharp -> 4
  | D      -> 5
  | Dsharp -> 6
  | E      -> 7
  | F      -> 8
  | Fsharp -> 9
  | G      -> 10
  | Gsharp -> 11
