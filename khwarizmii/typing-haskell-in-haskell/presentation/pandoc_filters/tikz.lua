-- The following will be parsed as the resulting raw Pandoc output:
--
-- Para [Image ("mytikzpic_id",["tikzpicture","mytikzpic_class1","mytikzpic_class2"],[("attr1","Random Attribute 1"),("attr2","Random Attribute 2")]) [Str "Some cool caption"] ("generated_figures/e75d31a59bc6689c3e4bc534d14be7231bb135f4.svg","fig:My Tikz Picture")]
--
--
-- \begin{tikzpicture}
-- % title:     My Tikz Picture
-- % caption:   Some cool caption
-- % id:        mytikzpic_id
-- % class:     mytikzpic_class1
-- % class:     mytikzpic_class2
-- % attr1:     Random Attribute 1
-- % attr2:     Random Attribute 2
--
-- \def \n {5}
-- \def \radius {3cm}
-- \def \margin {8} % margin in angles, depends on the radius
--
-- \foreach \s in {1,...,\n}
-- {
--   \node[draw, circle] at ({360/\n * (\s - 1)}:\radius) {$\s$};
--   \draw[->, >=latex] ({360/\n * (\s - 1)+\margin}:\radius)
--     arc ({360/\n * (\s - 1)+\margin}:{360/\n * (\s)-\margin}:\radius);
-- }
-- \end{tikzpicture}


local function tikz2image(src, filetype, outfile)
    local tmp = os.tmpname()
    local tmpdir = string.match(tmp, "^(.*[\\/])") or "."
    local f = io.open(tmp .. ".tex", 'w')
    f:write("\\documentclass{standalone}\n\\usepackage{xcolor}\n\\usepackage{tikz}\n\\begin{document}\n\\nopagecolor\n")
    f:write(src)
    f:write("\n\\end{document}\n")
    f:close()
    os.execute("pdflatex -output-directory " .. tmpdir  .. " " .. tmp)
    if filetype == 'pdf' then
        os.rename(tmp .. ".pdf", outfile)
    else
        os.execute("pdf2svg " .. tmp .. ".pdf " .. outfile)
    end
    os.remove(tmp .. ".tex")
    os.remove(tmp .. ".pdf")
    os.remove(tmp .. ".log")
    os.remove(tmp .. ".aux")
end

extension_for = {
    html = 'svg',
    html4 = 'svg',
    html5 = 'svg',
    latex = 'pdf',
    beamer = 'pdf' }

local function file_exists(name)
    local f = io.open(name, 'r')
    if f ~= nil then
        io.close(f)
        return true
    else
        return false
    end
end

local function starts_with(start, str)
   return str:sub(1, #start) == start
end

local function match_pattern(attribute)
   return "%s*%%[%%%s]+" .. attribute .. "%s*:%s*([^\n]+)"
end

local function match_attribute(text, attribute)
   return string.match(text, match_pattern(attribute))
end

local function parse_caption(text)
   local caption = match_attribute(text,"caption")
   if type(caption) == "string" then
      return { pandoc.Str(caption) }
   else
      return {}
   end
end

local function parse_title(text)
   local title = match_attribute(text,"title")
   if type(title) == "string" then
      if parse_caption(text) ~= {} then
         return "fig:" .. title
      else
         return title
      end
   else
      return ""
   end
end

local function parse_identifier(text)
   local id = match_attribute(text,"id")
   if type(id) == "string" then
      return id
   else
      return ""
   end
end

local function parse_classes(text)
   -- Always include tikzpicture as a class
   local classes = {"tikzpicture"}
   for class_name in string.gmatch(text, match_pattern("class")) do
      if type(class_name) == "string" then
         table.insert(classes, class_name)
      end
   end
   return classes
end

local function Set (list)
  local set = {}
  for _, l in ipairs(list) do set[l] = true end
  return set
end

local function parse_additional_image_attributes(text)
   local reserved_attribute_name = Set({"class", "title", "caption", "id"})
   local attributes = {}
   for key, value in string.gmatch(text, match_pattern("([^%s]+)")) do
      if     type(key) == "string"
         and type(value) == "string"
         and not reserved_attribute_name[key] then
            attributes[key] = value
      end
   end
   return attributes
end


function RawBlock(el)
    if starts_with("\\begin{tikzpicture}", el.text) then
        local filetype = extension_for[FORMAT] or "svg"
        local fname = "generated_figures/" .. pandoc.sha1(el.text) .. "." .. filetype
        if not file_exists(fname) then
            tikz2image(el.text, filetype, fname)
        end
        local caption = parse_caption(el.text)
        local title = parse_title(el.text)
        local id = parse_identifier(el.text)
        local classes = parse_classes(el.text)
        local image_attributes = parse_additional_image_attributes(el.text)
        return pandoc.Para({
              pandoc.Image(caption,
                           fname,
                           title,
                           pandoc.Attr(id,
                                       classes,
                                       image_attributes))
        })
    else
       return el
    end
end
