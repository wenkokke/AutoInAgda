require 'rake/clean'


DocDir = 'doc'
DocFiles = FileList["#{DocDir}/*.lagda",
                    "#{DocDir}/*.fmt"]
TeXFiles = FileList["#{DocDir}/main.tex",
                    "#{DocDir}/main.bib",
                    "#{DocDir}/preamble.tex" ]


desc "Compile and open the paper"
task :default => :build do
  system "open #{DocDir}/main.pdf"
end


desc "Compile the paper"
task :build => "#{DocDir}/main.pdf"


desc "Compile the paper"
file "#{DocDir}/main.pdf" => TeXFiles do
  Dir.chdir(DocDir) do

    system "pdflatex main.tex"
    if $?.success?
      system "bibtex main"
      if $?.success?
        system "pdflatex main.tex"
        system "pdflatex main.tex"
      end
    end

  end
end


desc "Compile literate Agda to TeX (and remove implicits)"
file "#{DocDir}/main.tex" => DocFiles do |t|

  f_abs   = File.absolute_path(t.name)
  f_lagda = f_abs.ext('.lagda')
  f_tex   = f_abs.ext('.tex')
  f_dir   = File.dirname(f_abs)

  Dir.chdir(f_dir) do

    cmd = "lhs2TeX --agda #{ f_lagda } -o #{ f_tex }"
    puts cmd
    system cmd

    fail "error in lhs2TeX" unless $?.success?

  end
end


TempPaperPats  = ['*.log','*.ptb','*.blg','*.bbl','*.aux','*.snm',
                  '*.toc','*.nav','*.out','auto','main.tex']
TempTeXFiles = FileList.new(TempPaperPats.map {|fn| File.join('paper',fn) })
TempCodePats   = ['*.agdai']
TempCodeFiles  = FileList.new(TempCodePats.map { |fn| File.join('code',fn) })

CLEAN.include(TempTeXFiles,TempCodeFiles)
CLOBBER.include('#{DocDir}/main.pdf')
