/**
 * Clase que prueba las implementaciones de los algoritmos observados en el
 * curso de "Algoritmos y Estructuras II" de la Universidad Simon Bolivar.
 * @version 0.1 23 de Enero de 2010
 * @author Victor De Ponte, 05-38087
 */
public class Main {

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) {
        String kg="";
        boolean salir=false;
        int n;
        do {
            n=Console.readInt("Por favor introduzca el tamano del arreglo (mayor o igual que cero):");
        } while (!(n>=0));
        int[] a=new int[n];
        Auxs.llenarA(a);
        int[] backup=new int[a.length];
        for (int k=0;k<a.length;k++) {
            backup[k]=a[k];
        }
        System.out.println("Arreglo cargado exitosamente...");
        do {
            System.out.println("\nBienvenido!\n\n\n");
            Auxs.print(a);
            System.out.println("\n\nQue desea hacer?\n\n\n");
            System.out.println("1) Ordenar el arreglo por el metodo 'Insercion'");
            System.out.println("2) Ordenar el arreglo por el metodo 'Seleccion'");
            System.out.println("3) Ordenar el arreglo por el metodo 'Burbuja'");
            System.out.println("4) Ordenar el arreglo por el metodo 'ShakeSort'");
            System.out.println("5) Ordenar el arreglo por el metodo 'MergeSort'");
            System.out.println("6) Ordenar el arreglo por el metodo 'QuickSort'");
            System.out.println("7) Buscar un elemento en el arreglo usando el metodo de 'busqueda lineal'.");
            System.out.println("8) Buscar un elemento en el arreglo usando el metodo de 'busqueda binaria'");
            System.out.println("   (el arreglo debe estar previamente ordenado).");
            System.out.println("9) Volver a desordenar el arreglo (devolverlo a su estado original).");
            System.out.println("10) Construir un arreglo nuevo (el anterior se pierde).");
            System.out.println("11) Salir del programa.");
            System.out.println("\n");
            
            int cmd;
            do {
                cmd=Console.readInt("Por favor introduzca una opcion valida:\n");
            } while (!(1<=cmd && cmd<=11));
            Auxs.print(a);
            if (cmd==1) {
                Ordenar.insercion(a);
                Auxs.printo(a);
            } else if (cmd==2) {
                Ordenar.seleccion(a);
                Auxs.printo(a);
            } else if (cmd==3) {
                System.out.println("Este metodo no esta implementado todavia...");
            } else if (cmd==4) {
                System.out.println("Este metodo no esta implementado todavia...");
            } else if (cmd==5) {
                Ordenar.mergesort(a);
                Auxs.printo(a);
            } else if (cmd==6) {
                System.out.println("Este metodo no esta implementado todavia...\n\n\n");
            } else if (cmd==7) {
                int e;
                do {
                    System.out.println("\nQue elemento desea buscar?\n");
                    System.out.println("1) El mayor elemento del arreglo");
                    System.out.println("2) El menor elemento del arreglo");
                    System.out.println("3) Un elemento introducido por usted\n");
                    e=Console.readInt("Introduzca una opcion valida: \n");
                } while (!(1<=e && e<=3));
                if (e==1) {
                    int pos=Buscar.linealM(a, 0, a.length);
                    System.out.println("\nEl MAYOR elemento del arreglo es "+a[pos]+" y se encuentra en la posicion "+pos+"\n");
                } else if (e==2) {
                    int pos=Buscar.linealm(a, 0, a.length);
                    System.out.println("\nEl MENOR elemento del arreglo es "+a[pos]+" y se encuentra en la posicion "+pos+"\n");
                } else if (e==3) {
                    int s;
                    do {
                        System.out.println("\nComo desea obtener la respuesta?\n");
                        System.out.println("1) En una variable booleana");
                        System.out.println("2) En un entero que devuelve la posicion, y si no esta devuelve -1");
                        s=Console.readInt("Introduzca una opcion valida: \n");
                    } while (!(1<=s&&s<=2));
                    e=Console.readInt("\nIntroduzca el elemento a buscar: \n");
                    if (s==1) {
                        boolean esta=Buscar.blineal(a, e);
                        if (esta) {
                            System.out.println("El elemento "+e+" SI ESTA en el arreglo...");
                        } else {
                            System.out.println("El elemento "+e+" NO ESTA en el arreglo...");
                        }
                    } else if (s==2) {
                        int pos=Buscar.lineal(a, e);
                        if (0<=pos && pos<=a.length) {
                            System.out.println("El elemento "+e+" SI ESTA en el arreglo y esta en la posicion "+pos);
                        } else {
                            System.out.println("El elemento "+e+" NO ESTA en el arreglo...");
                        }
                    }
                }
                
            } else if (cmd==8) {
                int e=Console.readInt("\nIntroduzca el elemento a buscar: \n");
                int s;
                do {
                    System.out.println("\nComo desea obtener la respuesta?\n");
                    System.out.println("1) En una variable booleana");
                    System.out.println("2) El un entero que devuelve la posicion, y si no esta, devuelve -1");
                    s=Console.readInt("Introduzca una opcion valida: \n");
                } while (!(1<=s&&s<=2));
                if (s==1) {
                    boolean esta=Buscar.bbinaria(a, e);
                    if (esta) {
                        System.out.println("El elemento "+e+" SI ESTA en el arreglo...");
                    } else {
                        System.out.println("El elemento "+e+" NO ESTA en el arreglo...");
                    }
                } else {
                    int pos=Buscar.binaria(a, e);
                    if (0<=pos && pos<=a.length) {
                        System.out.println("El elemento "+e+" SI ESTA en el arreglo y esta en la posicion "+pos);
                    } else {
                        System.out.println("El elemento "+e+" NO ESTA en el arreglo...");
                    }
                }
            } else if (cmd==9) {
                for (int k=0;k<backup.length; k++) {
                    a[k]=backup[k];
                }
            } else if (cmd==10) {
                int[] aux= new int[Console.readInt("Ingrese el tamano del arreglo nuevo: \n")];
                Auxs.llenarA(aux);
                for (int k=0;k<a.length;k++) {
                    backup[k]=a[k];
                }
                a=aux;
                System.out.println("Arreglo generado y cargado exitosamente...");
                Auxs.print(a);
            } else if (cmd==11) {
                salir=true;
                kg="no";
            }
            do {
                if (!salir) {
                    kg=Console.readString("Desea volver a intentarlo? (yes/y/si/s/no/n):\n\n");
                }
            } while (!(kg.equalsIgnoreCase("yes")||kg.equalsIgnoreCase("y")||kg.equalsIgnoreCase("si")||kg.equalsIgnoreCase("s")||kg.equalsIgnoreCase("no")||kg.equalsIgnoreCase("n")));
        } while (kg.equalsIgnoreCase("yes")||kg.equalsIgnoreCase("y")||kg.equalsIgnoreCase("si")||kg.equalsIgnoreCase("s"));
        System.out.println("\nHasta Luego!!! Gracias por usar este programa...\n\n\n");
    }
}