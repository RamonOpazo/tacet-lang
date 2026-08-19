local function is_chapter_heading(el)
  return el.t == "Header" and el.level == 1
    and pandoc.utils.stringify(el.content):match("^Chapter%f[%A]")
end

-- Unwrap ```tikz fenced code blocks (written as standalone
-- preamble+document snippets) into raw tikzcd bodies; the packages
-- they declare are already loaded globally by main.latex.
local function unwrap_tikz(el)
  if el.classes[1] ~= "tikz" then return nil end
  local body = el.text
  body = body:gsub("\\usepackage{[^}]*}\n?", "")
  body = body:gsub("\\begin{document}\n?", "")
  body = body:gsub("\\end{document}\n?", "")
  return pandoc.RawBlock("latex", body)
end

function Pandoc(doc)
  local blocks = doc.blocks

  -- Drop any leading blocks (doc title, byline, rule) before the
  -- first chapter heading; the title page is rendered by main.latex's
  -- own \maketitle instead.
  local start = 1
  for i, el in ipairs(blocks) do
    if is_chapter_heading(el) then
      start = i
      break
    end
  end
  local kept = {}
  for i = start, #blocks do
    table.insert(kept, blocks[i])
  end
  doc.blocks = kept

  doc = doc:walk({ CodeBlock = unwrap_tikz })

  return doc
end
