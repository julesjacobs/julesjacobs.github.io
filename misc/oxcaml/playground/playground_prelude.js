export const playgroundPreludeSource = String.raw`module Oxcaml_playground_repr = struct
  let print_html html =
    print_endline "%%OXCAML_HTML_BEGIN%%";
    print_endline html;
    print_endline "%%OXCAML_HTML_END%%"

  let escape_html text =
    let b = Buffer.create (String.length text) in
    String.iter
      (function
        | '&' -> Buffer.add_string b "&amp;"
        | '<' -> Buffer.add_string b "&lt;"
        | '>' -> Buffer.add_string b "&gt;"
        | '"' -> Buffer.add_string b "&quot;"
        | '\'' -> Buffer.add_string b "&#39;"
        | c -> Buffer.add_char b c)
      text;
    Buffer.contents b

  let add = Buffer.add_string

  let tag_name tag =
    if tag = Obj.string_tag then "string"
    else if tag = Obj.double_tag then "double"
    else if tag = Obj.double_array_tag then "double_array"
    else if tag = Obj.closure_tag then "closure"
    else if tag = Obj.object_tag then "object"
    else if tag = Obj.lazy_tag then "lazy"
    else if tag = Obj.forward_tag then "forward"
    else if tag = Obj.abstract_tag then "abstract/no_scan"
    else if tag = Obj.custom_tag then "custom"
    else if tag >= Obj.no_scan_tag then "no_scan"
    else "scannable"

  let mixed_scannable_prefix obj =
    if Obj.is_int obj || Obj.tag obj >= Obj.no_scan_tag
    then None
    else (
      match Obj.Uniform_or_mixed.(repr (of_block obj)) with
      | Uniform -> None
      | Mixed { scannable_prefix_len } -> Some scannable_prefix_len)

  let graph_counter = ref 0

  let css =
    {|
<style>
  .repr-graph {
    color: #0f172a;
    font-family: ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
    padding: 16px;
  }
  .repr-title {
    align-items: baseline;
    display: flex;
    gap: 12px;
    margin: 0 0 12px;
  }
  .repr-title h3 {
    font-size: 18px;
    margin: 0;
  }
  .repr-title span, .repr-note, .repr-raw {
    color: #64748b;
  }
  .repr-node, .repr-immediate {
    background: #ffffff;
    border: 1px solid #cbd5e1;
    border-radius: 8px;
    margin: 10px 0;
    overflow: hidden;
  }
  .repr-node header, .repr-immediate {
    align-items: center;
    display: flex;
    flex-wrap: wrap;
    gap: 8px;
    padding: 10px 12px;
  }
  .repr-node header {
    background: #f8fafc;
    border-bottom: 1px solid #e2e8f0;
  }
  .repr-node strong, .repr-node td, .repr-immediate code {
    font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace;
  }
  .repr-node strong, .repr-edge {
    color: #0f766e;
    font-weight: 700;
  }
  .repr-chip {
    background: #e2e8f0;
    border-radius: 999px;
    color: #334155;
    font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace;
    font-size: 12px;
    padding: 2px 8px;
  }
  .repr-node table {
    border-collapse: collapse;
    width: 100%;
  }
  .repr-node td {
    border-top: 1px solid #eef2f7;
    font-size: 13px;
    padding: 8px 10px;
    vertical-align: top;
  }
  .repr-node tr:first-child td {
    border-top: 0;
  }
  .repr-index {
    color: #64748b;
    width: 64px;
  }
  .repr-note {
    font-size: 13px;
    margin-top: 12px;
  }
</style>
|}

  let inspect name value =
    incr graph_counter;
    let graph_id = !graph_counter in
    let max_nodes = 80 in
    let next_id = ref 1 in
    let ids = ref [] in
    let queue = Queue.create () in
    let truncated = ref false in
    let find_id obj =
      List.find_map
        (fun (seen, id) -> if seen == obj then Some id else None)
        !ids
    in
    let enqueue obj =
      match find_id obj with
      | Some id -> id
      | None ->
        if !next_id > max_nodes
        then (
          truncated := true;
          0)
        else (
          let id = !next_id in
          incr next_id;
          ids := (obj, id) :: !ids;
          Queue.add obj queue;
          id)
    in
    let anchor id = Printf.sprintf "repr-%d-node-%d" graph_id id in
    let b = Buffer.create 4096 in
    add b css;
    Printf.bprintf
      b
      "<div class='repr-graph'><div class='repr-title'><h3>%s</h3><span>OCaml value graph</span></div>"
      (escape_html name);
    let root = Obj.repr value in
    if Obj.is_int root
    then
      Printf.bprintf
        b
        "<div class='repr-immediate'><span class='repr-chip'>immediate</span><code>%d</code></div>"
        (Obj.obj root : int)
    else (
      let root_id = enqueue root in
      Printf.bprintf
        b
        "<p class='repr-note'>root <a class='repr-edge' href='#%s'>@%d</a></p>"
        (anchor root_id)
        root_id;
      while not (Queue.is_empty queue) do
        let obj = Queue.take queue in
        let id =
          match find_id obj with
          | Some id -> id
          | None -> assert false
        in
        let tag = Obj.tag obj in
        let size = Obj.size obj in
        let scannable_prefix =
          match mixed_scannable_prefix obj with
          | None -> size
          | Some prefix -> prefix
        in
        let mixed_label =
          match mixed_scannable_prefix obj with
          | None -> ""
          | Some prefix -> Printf.sprintf "<span class='repr-chip'>mixed scan prefix %d</span>" prefix
        in
        let size_label =
          if tag >= Obj.no_scan_tag
          && tag <> Obj.double_tag
          && tag <> Obj.double_array_tag
          then "raw data"
          else Printf.sprintf "%d words" size
        in
        Printf.bprintf
          b
          "<section class='repr-node' id='%s'><header><strong>@%d</strong><span class='repr-chip'>tag %d %s</span><span class='repr-chip'>%s</span>%s</header><table><tbody>"
          (anchor id)
          id
          tag
          (escape_html (tag_name tag))
          size_label
          mixed_label;
        let row i body =
          Printf.bprintf b "<tr><td class='repr-index'>[%d]</td><td>%s</td></tr>" i body
        in
        if tag = Obj.double_tag
        then row 0 (Printf.sprintf "double %h" (Obj.double_field obj 0))
        else if tag = Obj.double_array_tag
        then
          for i = 0 to size - 1 do
            row i (Printf.sprintf "double %h" (Obj.double_field obj i))
          done
        else if tag >= Obj.no_scan_tag
        then row 0 "<span class='repr-raw'>raw/no-scan data</span>"
        else
          for i = 0 to size - 1 do
            if i >= scannable_prefix
            then row i "<span class='repr-raw'>raw unscanned word</span>"
            else
              let field = Obj.field obj i in
              if Obj.is_int field
              then
                row
                  i
                  (Printf.sprintf "immediate %d" (Obj.obj field : int))
              else (
                let child_id = enqueue field in
                if child_id = 0
                then row i "<span class='repr-raw'>truncated edge</span>"
                else
                  row
                    i
                    (Printf.sprintf
                       "<a class='repr-edge' href='#%s'>-&gt; @%d</a>"
                       (anchor child_id)
                       child_id))
          done;
        add b "</tbody></table></section>"
      done);
    if !truncated
    then add b "<p class='repr-note'>Traversal stopped at the node limit.</p>";
    add b "<p class='repr-note'>Only ordinary OCaml values can be inspected directly. Fields outside a mixed block's scannable prefix are unboxed data, so the visualizer does not treat them as OCaml values.</p></div>";
    print_html (Buffer.contents b)
end

let show_repr_named name value = Oxcaml_playground_repr.inspect name value
let show_repr value = show_repr_named "value" value
;;
`;

function ocamlEscapedStringLiteral(text) {
  return `"${String(text)
    .replace(/\\/g, "\\\\")
    .replace(/"/g, "\\\"")
    .replace(/\n/g, "\\n")
    .replace(/\r/g, "\\r")
    .replace(/\t/g, "\\t")}"`;
}

export function withPlaygroundPrelude(filename, source) {
  return [
    playgroundPreludeSource,
    `# 1 ${ocamlEscapedStringLiteral(filename)}`,
    source,
  ].join("\n");
}

export function stripPlaygroundPreludeInterface(output) {
  return String(output)
    .replace(/^module Oxcaml_playground_repr :\n\s*sig\n[\s\S]*?\n\s*end\n/m, "")
    .replace(/^val show_repr_named : [^\n]*\n/m, "")
    .replace(/^val show_repr : [^\n]*\n/m, "")
    .replace(/^\s+/, "");
}
