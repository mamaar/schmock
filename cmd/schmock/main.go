package main

import (
	"cmp"
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io"
	"os"
	"slices"
)

type MockType string

var (
	Interface MockType = "interface"
	Struct    MockType = "struct"
)

type param struct {
	name string
	typ  string
}

type method struct {
	name    string
	params  []param
	returns []param
}

type mock struct {
	name    string
	methods []method
}

func main() {
	var (
		packagePath    = flag.String("path", "", "path to the package to be mocked")
		implementation = flag.String("implementation", "", "the type in the package to be mocked")
		outputFileName = flag.String("output", "", "output file")
		mockName       = flag.String("mock", "Mock", "name of the mock output struct")
		mockT          = flag.String("type", "", "type of the mock output (struct or interface)")
	)
	flag.Parse()

	var mockType MockType
	switch *mockT {
	case "struct":
		mockType = Struct
	case "interface":
		mockType = Interface
	default:
		_, _ = os.Stderr.WriteString("Invalid mock type. Must be 'struct' or 'interface'.\n")
		os.Exit(1)
	}

	if *packagePath == "" || *implementation == "" || *outputFileName == "" {
		_, _ = os.Stderr.WriteString("Usage: schmock -path <package path> -type <type> -output <output file>\n")
		os.Exit(1)
	}

	fset := token.NewFileSet()

	fileMap, err := parser.ParseDir(fset, *packagePath, nil, parser.ParseComments)
	if err != nil {
		os.Stderr.WriteString("Error parsing package: " + err.Error() + "\n")
		os.Exit(1)
	}

	schmock := mock{}

	// We iterate over the declarations in all Go files in the package
	for _, file := range fileMap {
		for _, f := range file.Files {
			for _, decl := range f.Decls {

				// We only care about function declarations that also have a receiver.
				// This is because we're looking for methods to mock.
				switch d := decl.(type) {
				case *ast.FuncDecl:
					if d.Recv == nil {
						continue
					}

					for _, field := range d.Recv.List {
						switch t := field.Type.(type) {
						case *ast.StarExpr:
							if ident, ok := t.X.(*ast.Ident); ok {

								if ident.Name == *implementation {
									isExported := token.IsExported(d.Name.Name)
									if !isExported {
										continue
									}

									methodName := d.Name.Name
									m := method{name: methodName}

									for _, p := range d.Type.Params.List {
										switch pType := p.Type.(type) {
										case *ast.SelectorExpr:
											paramTypeName := pType.X.(*ast.Ident).Name
											paramTypeSel := pType.Sel.Name
											paramTypeFmt := fmt.Sprintf("%s.%s", paramTypeName, paramTypeSel)
											for _, n := range p.Names {
												m.params = append(m.params, param{name: n.Name, typ: paramTypeFmt})
											}
										case *ast.Ident:
											for _, n := range p.Names {
												m.params = append(m.params, param{name: n.Name, typ: pType.Name})
											}
										default:
											continue
										}
									}

									for _, r := range d.Type.Results.List {
										switch rType := r.Type.(type) {
										case *ast.ArrayType:
											switch x := rType.Elt.(type) {
											case *ast.SelectorExpr:
												paramTypeName := x.X.(*ast.Ident).Name
												paramTypeSel := x.Sel.Name
												paramTypeFmt := fmt.Sprintf("%s.%s", paramTypeName, paramTypeSel)
												if len(r.Names) == 0 {
													m.returns = append(m.returns, param{name: "", typ: "[]" + paramTypeFmt})
												} else {
													for _, n := range r.Names {
														m.returns = append(m.returns, param{name: n.Name, typ: "[]" + paramTypeFmt})
													}
												}
											}
										case *ast.StarExpr:
											switch x := rType.X.(type) {
											case *ast.SelectorExpr:
												paramTypeName := x.X.(*ast.Ident).Name
												paramTypeSel := x.Sel.Name
												paramTypeFmt := fmt.Sprintf("%s.%s", paramTypeName, paramTypeSel)
												if len(r.Names) == 0 {
													m.returns = append(m.returns, param{name: "", typ: "*" + paramTypeFmt})
												} else {
													for _, n := range r.Names {
														m.returns = append(m.returns, param{name: n.Name, typ: "*" + paramTypeFmt})
													}
												}
											}
										case *ast.SelectorExpr:
											paramTypeName := rType.X.(*ast.Ident).Name
											paramTypeSel := rType.Sel.Name
											paramTypeFmt := fmt.Sprintf("%s.%s", paramTypeName, paramTypeSel)
											if len(r.Names) == 0 {
												m.returns = append(m.returns, param{name: "", typ: paramTypeFmt})
											} else {
												for _, n := range r.Names {
													m.returns = append(m.returns, param{name: n.Name, typ: paramTypeFmt})
												}
											}
										case *ast.Ident:
											if len(r.Names) == 0 {
												m.returns = append(m.returns, param{name: "", typ: rType.Name})
											} else {
												for _, n := range r.Names {
													m.returns = append(m.returns, param{name: n.Name, typ: rType.Name})
												}
											}
										default:
											continue
										}
									}

									schmock.methods = append(schmock.methods, m)
								}
							}
						}
					}
				}
			}
		}
	}

	schmock.methods = slices.SortedFunc(slices.Values(schmock.methods), func(i method, j method) int {
		return cmp.Compare(i.name, j.name)
	})

	var outputFile io.Writer

	if *outputFileName == "-" {
		outputFile = os.Stdout
	} else {
		outputFile, err = os.Create(*outputFileName)
		if err != nil {
			os.Stderr.WriteString("Error creating output file: " + err.Error() + "\n")
			os.Exit(1)
		}
		if closer, ok := outputFile.(io.Closer); ok {
			defer closer.Close()
		}
	}

	_, err = fmt.Fprintf(outputFile, "package mock\n\n")
	if err != nil {
		_, _ = os.Stderr.WriteString("Error writing package statement: " + err.Error() + "\n")
		os.Exit(1)
	}

	err = writeType(outputFile, mockType, mockName, schmock)
	if err != nil {
		_, _ = os.Stderr.WriteString("Error writing type: " + err.Error() + "\n")
		os.Exit(1)
	}

	if mockType == Interface {
		return
	}

	// Write the implementation of the methods
	for _, m := range schmock.methods {
		_, err = fmt.Fprintf(outputFile, "func (m *%s) %s", *mockName, m.name)
		if err != nil {
			_, _ = os.Stderr.WriteString("Error writing method signature: " + err.Error() + "\n")
			os.Exit(1)
		}

		err = writeParameters(outputFile, m.params)
		if err != nil {
			_, _ = os.Stderr.WriteString("Error writing parameters: " + err.Error() + "\n")
			os.Exit(1)
		}

		err = writeReturns(outputFile, m.returns)
		if err != nil {
			_, _ = os.Stderr.WriteString("Error writing returns: " + err.Error() + "\n")
			os.Exit(1)
		}

		err = writeImplementation(outputFile, m)
		if err != nil {
			_, _ = os.Stderr.WriteString("Error writing implementation: " + err.Error() + "\n")
			os.Exit(1)
		}

		_, err = fmt.Fprintf(outputFile, "\n}\n\n")
		if err != nil {
			_, _ = os.Stderr.WriteString("Error writing closing brace: " + err.Error() + "\n")
			os.Exit(1)
		}
	}

}

// writeType writes the struct or interface definition for the mock.
// If the type is interface, it writes the interface definition.
// If the type is struct, it writes the struct definition with fields for each method.
func writeType(outputFile io.Writer, typ MockType, mockName *string, schmock mock) error {
	var err error

	// The struct type will add a "Func" suffix to the method names that will be used to store the function pointers.
	methodSuffix := ""

	// The type name will be either "interface" or "struct".
	typeName := ""

	switch typ {
	case Interface:
		typeName = "interface"
		methodSuffix = ""
	case Struct:
		typeName = "struct"
		methodSuffix = "Func"
	}

	_, err = fmt.Fprintf(outputFile, "type %s %s {\n", *mockName, typeName)
	if err != nil {
		return fmt.Errorf("error writing %s definition: %w", typeName, err)
	}
	for _, m := range schmock.methods {
		_, err = fmt.Fprintf(outputFile, "\t%s%s", m.name, methodSuffix)
		if err != nil {
			return fmt.Errorf("error writing type field: %w", err)
		}

		_, err = fmt.Fprintf(outputFile, "(")
		if err != nil {
			return fmt.Errorf("error writing parameter opening parenthesis: %w", err)
		}

		for i, p := range m.params {
			_, err = fmt.Fprintf(outputFile, "%s %s", p.name, p.typ)
			if err != nil {
				return fmt.Errorf("error writing parameter %s %s: %w", p.name, p.typ, err)
			}
			if i < len(m.params)-1 {
				_, err = fmt.Fprintf(outputFile, ", ")
				if err != nil {
					return fmt.Errorf("error writing comma: %w", err)
				}
			}
		}
		_, err = fmt.Fprintf(outputFile, ")")
		if err != nil {
			return fmt.Errorf("error writing parameter closing parenthesis: %w", err)
		}

		switch len(m.returns) {
		case 0:
			_, err = fmt.Fprintf(outputFile, "\n")
			if err != nil {
				return fmt.Errorf("error writing zero return values newline: %w", err)
			}
		case 1:
			_, err = fmt.Fprintf(outputFile, " %s\n", m.returns[0].typ)
			if err != nil {
				return fmt.Errorf("error writing single return value %s: %w", m.returns[0].typ, err)
			}
		default:
			_, err = fmt.Fprintf(outputFile, " (")
			if err != nil {
				return fmt.Errorf("error writing multiple return values opening parenthesis: %w", err)
			}

			for i, r := range m.returns {
				_, err = fmt.Fprintf(outputFile, "%s", r.typ)
				if err != nil {
					return fmt.Errorf("error writing multiple return value %s: %w", r.typ, err)
				}

				if i < len(m.returns)-1 {
					_, err = fmt.Fprintf(outputFile, ", ")
					if err != nil {
						return fmt.Errorf("error writing multiple return values comma: %w", err)
					}
				}
			}

			_, err = fmt.Fprintf(outputFile, ")\n")
			if err != nil {
				return fmt.Errorf("error writing multiple return values closing parenthesis: %w", err)
			}
		}
	}

	_, err = fmt.Fprintf(outputFile, "}\n\n")
	if err != nil {
		return fmt.Errorf("error writing type closing brace: %w", err)
	}

	return nil
}

func writeImplementation(outputFile io.Writer, m method) error {
	var err error

	_, err = fmt.Fprintf(outputFile, " {\n")
	if err != nil {
		return fmt.Errorf("error writing function opening brace: %w", err)
	}

	_, err = fmt.Fprintf(outputFile, "\tif m.%sFunc != nil {\n", m.name)
	if err != nil {
		return fmt.Errorf("error writing if overridden statement: %w", err)
	}

	_, err = fmt.Fprintf(outputFile, "\t\treturn m.%sFunc(", m.name)
	if err != nil {
		return fmt.Errorf("error writing function call: %w", err)
	}

	for i, p := range m.params {
		_, err = fmt.Fprintf(outputFile, "%s", p.name)
		if err != nil {
			return fmt.Errorf("error writing function call parameter %s: %w", p.name, err)
		}
		if i < len(m.params)-1 {
			_, err = fmt.Fprintf(outputFile, ", ")
			if err != nil {
				return fmt.Errorf("error writing function call comma: %w", err)
			}
		}
	}

	_, err = fmt.Fprintf(outputFile, ")\n")
	if err != nil {
		return fmt.Errorf("error writing function call closing parenthesis: %w", err)
	}

	_, err = fmt.Fprintf(outputFile, "\t}\n\n")
	if err != nil {
		return fmt.Errorf("error writing if overridden closing brace: %w", err)
	}

	// The function is not overridden, so we return zero values for the return types.
	// We do this by declaring variables for the return types and returning them.
	//    var (
	//    	r0 string
	//    	r1 int
	//    )
	//    return r0, r1
	_, err = fmt.Fprintf(outputFile, "\tvar (\n")
	if err != nil {
		return fmt.Errorf("error writing return variable opening parenthesis: %w", err)
	}

	for i, r := range m.returns {
		_, err = fmt.Fprintf(outputFile, "\t\tr%d %s\n", i, r.typ)
		if err != nil {
			return fmt.Errorf("error writing return variable (%d) %s: %w", i, r.typ, err)
		}
	}

	_, err = fmt.Fprintf(outputFile, "\t)\n\n")
	if err != nil {
		return fmt.Errorf("error writing return variable closing parenthesis: %w", err)
	}

	_, err = fmt.Fprintf(outputFile, "\treturn ")
	if err != nil {
		return fmt.Errorf("error writing zero value return statement: %w", err)
	}
	for i := range m.returns {
		_, err = fmt.Fprintf(outputFile, "r%d", i)
		if err != nil {
			return fmt.Errorf("error writing zero value return statement (%d): %w", i, err)
		}
		if i < len(m.returns)-1 {
			_, err = fmt.Fprintf(outputFile, ", ")
			if err != nil {
				return fmt.Errorf("error writing zero value return statement comma: %w", err)
			}
		}
	}

	return nil
}

func writeReturns(outputFile io.Writer, returns []param) error {
	var err error

	if len(returns) == 1 {
		_, err = fmt.Fprintf(outputFile, " %s", returns[0].typ)
		if err != nil {
			return fmt.Errorf("error writing single return %s: %w", returns[0].typ, err)
		}
		return nil
	}

	_, err = fmt.Fprintf(outputFile, " (")
	if err != nil {
		return fmt.Errorf("error writing opening parenthesis: %w", err)
	}

	for i, r := range returns {
		_, err = fmt.Fprintf(outputFile, "%s", r.typ)
		if err != nil {
			return fmt.Errorf("error writing unnamed return (%d) %s: %w", i, r.typ, err)
		}

		if i < len(returns)-1 {
			_, err = fmt.Fprintf(outputFile, ", ")
			if err != nil {
				return fmt.Errorf("error writing comma: %w", err)
			}
		}
	}

	_, err = fmt.Fprintf(outputFile, ")")
	if err != nil {
		return fmt.Errorf("error writing closing parenthesis: %w", err)
	}

	return nil
}

func writeParameters(w io.Writer, params []param) error {
	var err error

	_, err = fmt.Fprintf(w, "(")
	if err != nil {
		return fmt.Errorf("error writing opening parenthesis: %w", err)
	}

	for i, p := range params {
		_, err = fmt.Fprintf(w, "%s %s", p.name, p.typ)
		if err != nil {
			return fmt.Errorf("error writing parameter (%d) %s %s: %w", i, p.name, p.typ, err)
		}

		if i < len(params)-1 {
			_, err = fmt.Fprintf(w, ", ")
			if err != nil {
				return fmt.Errorf("error writing comma: %w", err)
			}
		}
	}
	_, err = fmt.Fprintf(w, ")")
	if err != nil {
		return fmt.Errorf("error writing closing parenthesis: %w", err)
	}

	return nil
}
